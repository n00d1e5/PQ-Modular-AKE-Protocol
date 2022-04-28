#include "inttypes.h"
#include "ntt.h"
#include "params.h"
#include "reduce.h"

/*************************************************
* Name:        ntt
*
* Description: Computes number-theoretic transform (NTT) of
*              a polynomial in place; inputs assumed to be in
*              normal order, output in bitreversed order
*
* Arguments:   - int16_t * a:           pointer to in/output polynomial
*              - const int16_t* gammas: pointer to input powers of root of unity gamma;
*                                       assumed to be in Montgomery domain
**************************************************/
void ntt(int16_t *a, const int16_t *gammas)
{
  int k, len, start, j;
  int16_t G, temp;
  
  k = 1;
  for(len = NEWHOPE_NTT_LENGTH/2; len >= 1; len >>= 1) {
#if (NEWHOPE_N == 768)
    if(len==NEWHOPE_NTT_LENGTH/2) {
      G = gammas[k++];
      for(j = 0; j < len; ++j) {
        temp = montgomery_reduce(G * a[j + len]);
        a[j + len] = a[j] + a[j + len] - temp;
        a[j] = a[j] + temp;
      }

      len >>= 1;
    }
#endif
    for(start = 0; start < NEWHOPE_NTT_LENGTH; start = j + len) {
      G = gammas[k++];
      for(j = start; j < start + len; ++j) {
        temp = montgomery_reduce(G * a[j + len]);
        a[j + len] = a[j] - temp; // Omit reduction (be lazy)   
        a[j] = a[j] + temp; // Omit reduction (be lazy)
      }
    }
  }
}

/*************************************************
* Name:        invntt
*
* Description: Computes inverse number-theoretic transform (INTT) of
*              a polynomial in place; inputs assumed to be in
*              bitreversed order, output in normal order
*
* Arguments:   - int16_t * a:           pointer to in/output polynomial
*              - const int16_t* gammas: pointer to input powers of root of unity gamma;
*                                       assumed to be in Montgomery domain
**************************************************/
void invntt(int16_t *a, const int16_t *gammas)
{
  int k, len, start, j;
  int16_t temp, G;

  k = 0;
  for(len = 1; len <= NEWHOPE_NTT_LENGTH/2; len <<= 1) {
#if (NEWHOPE_N == 768)
    if(len==NEWHOPE_NTT_LENGTH/2) {
      for(j=0;j<len;++j) {
        temp = a[j] - a[j + len];
        temp = montgomery_reduce(gammas[NEWHOPE_NTT_LENGTH-2] * temp);
        a[j] = a[j] + a[j + len];
        a[j] = a[j] - temp;
        a[j] = montgomery_reduce(gammas[NEWHOPE_NTT_LENGTH-1] * a[j]);
        a[j + len] = montgomery_reduce(gammas[NEWHOPE_NTT_LENGTH] * temp);
      }
      
      break;
    }
#endif
    for(start = 0; start < NEWHOPE_NTT_LENGTH; start = j + len) {
      G = gammas[k++];
      for(j = start; j < start + len; ++j) {
        temp = a[j];
        a[j] = barrett_reduce(temp + a[j + len]);
        a[j + len] = montgomery_reduce(G * (temp - a[j + len]));
      }
    }
  }

#if (NEWHOPE_N != 768)
  for(j=0;j<NEWHOPE_NTT_LENGTH;j++)
    a[j] = montgomery_reduce(a[j] * gammas[k]);
#endif
}

#if USE_SCHOOLBOOK_MULTIPLICATION

/*************************************************
* Name:        basemul
*
* Description: Multiply two polynomials in Zq[X]/(X^NEWHOPE_NTT_POLY-gamma) 
*
* Arguments:   - poly *r:       pointer to output polynomial
*              - const poly *a: pointer to first input polynomial
*              - const poly *b: pointer to second input polynomial
**************************************************/
void basemul(int16_t *r, const int16_t *a, const int16_t *b, int16_t gamma)
{
  int i,j;
  
  for(i=0;i<NEWHOPE_NTT_POLY;i++)
  {
    r[i*NEWHOPE_NTT_LENGTH] = 0;
    for(j=i+1;j<NEWHOPE_NTT_POLY;j++)
      r[i*NEWHOPE_NTT_LENGTH] += 
        montgomery_reduce(a[j*NEWHOPE_NTT_LENGTH] * b[(NEWHOPE_NTT_POLY+i-j)*NEWHOPE_NTT_LENGTH]);
    if (j!=i+1)
      r[i*NEWHOPE_NTT_LENGTH] = montgomery_reduce(r[i*NEWHOPE_NTT_LENGTH] * gamma);
    for(j=0;j<i+1;j++)
      r[i*NEWHOPE_NTT_LENGTH] += 
        montgomery_reduce(a[j*NEWHOPE_NTT_LENGTH] * b[(i-j)*NEWHOPE_NTT_LENGTH]);
  }
}

#elif USE_KARATSUBA_MULTIPLICATION

#define NTT_LENGTH(x) (x*NEWHOPE_NTT_LENGTH)

#define CALC_D(a,b,x,y,d) (montgomery_reduce((a[NTT_LENGTH(x)]+a[NTT_LENGTH(y)])* \
                                             (b[NTT_LENGTH(x)]+b[NTT_LENGTH(y)]))-d[x]-d[y])

/*************************************************
* Name:        basemul
*
* Description: Multiply two polynomials in Zq[X]/(X^NEWHOPE_NTT_POLY-gamma) 
*
* Arguments:   - poly *r:       pointer to output polynomial
*              - const poly *a: pointer to first input polynomial
*              - const poly *b: pointer to second input polynomial
**************************************************/
void basemul(int16_t *r, const int16_t *a, const int16_t *b, int16_t gamma)
{ 
  int i;

  int16_t d[NEWHOPE_NTT_POLY];
  for(i=0;i<NEWHOPE_NTT_POLY;i++)
    d[i] = montgomery_reduce(a[i*128]*b[i*128]);  

#if   (NEWHOPE_N == 512)
  
  r[NTT_LENGTH(0)] = d[0] + 
         montgomery_reduce(
           (CALC_D(a, b, 1, 3, d)+d[2]) * gamma);
  
  r[NTT_LENGTH(1)] = CALC_D(a, b, 0, 1, d)+
         montgomery_reduce(
           CALC_D(a, b, 2, 3, d) * gamma);
  
  r[NTT_LENGTH(2)] = barrett_reduce(CALC_D(a, b, 0, 2, d)+d[1]+ 
         montgomery_reduce(d[3] * gamma));
  
  r[NTT_LENGTH(3)] = barrett_reduce(CALC_D(a, b, 1, 2, d)+ 
         CALC_D(a, b, 0, 3, d));
  
#elif (NEWHOPE_N == 768)
  
  r[NTT_LENGTH(0)] = d[0] + 
         montgomery_reduce(
           (CALC_D(a, b, 1, 5, d)+
            CALC_D(a, b, 2, 4, d)+d[3]) * gamma);
  
  r[NTT_LENGTH(1)] = CALC_D(a, b, 0, 1, d)+ 
         montgomery_reduce(
           (CALC_D(a, b, 2, 5, d)+
            CALC_D(a, b, 3, 4, d)) * gamma);
  
  r[NTT_LENGTH(2)] = barrett_reduce(
          CALC_D(a, b, 0, 2, d)+d[1]+ 
          montgomery_reduce(
            (CALC_D(a, b, 3, 5, d)+d[4]) * gamma));
  
  r[NTT_LENGTH(3)] = barrett_reduce(
          CALC_D(a, b, 0, 3, d)+ 
          CALC_D(a, b, 1, 2, d)+
          montgomery_reduce(
            CALC_D(a, b, 4, 5, d) * gamma));
  
  r[NTT_LENGTH(4)] = barrett_reduce(
           CALC_D(a, b, 0, 4, d)+
             CALC_D(a, b, 1, 3, d)+d[2]+ 
             montgomery_reduce(d[5] * gamma));
  
  r[NTT_LENGTH(5)] = barrett_reduce(CALC_D(a, b, 0, 5, d)+
         CALC_D(a, b, 1, 4, d))+
         CALC_D(a, b, 2, 3, d);
  
#elif (NEWHOPE_N == 1024)
  
  r[NTT_LENGTH(0)] = d[0] + 
         montgomery_reduce(
           (CALC_D(a, b, 1, 7, d)+
            CALC_D(a, b, 2, 6, d)+
            CALC_D(a, b, 3, 5, d)+d[4]) * gamma);
  
  r[NTT_LENGTH(1)] = CALC_D(a, b, 0, 1, d)+ 
         montgomery_reduce(
           (CALC_D(a, b, 2, 7, d)+
            CALC_D(a, b, 3, 6, d)+
            CALC_D(a, b, 4, 5, d)) * gamma);
  
  r[NTT_LENGTH(2)] = barrett_reduce(CALC_D(a, b, 0, 2, d)+d[1]+ 
         montgomery_reduce(
           (CALC_D(a, b, 3, 7, d)+
            CALC_D(a, b, 4, 6, d)+d[5]) * gamma));
  
  r[NTT_LENGTH(3)] = barrett_reduce(CALC_D(a, b, 0, 3, d)+
         CALC_D(a, b, 1, 2, d)+
         montgomery_reduce(
           (CALC_D(a, b, 4, 7, d)+
            CALC_D(a, b, 5, 6, d))* gamma));

  r[NTT_LENGTH(4)] = barrett_reduce(CALC_D(a, b, 0, 4, d)+
         CALC_D(a, b, 1, 3, d)+ d[2]+ 
         montgomery_reduce(
           (CALC_D(a, b, 5, 7, d)+d[6]) * gamma));  

  r[NTT_LENGTH(5)] = barrett_reduce(CALC_D(a, b, 0, 5, d)+
         CALC_D(a, b, 1, 4, d)+
         CALC_D(a, b, 2, 3, d))+
         montgomery_reduce(
           CALC_D(a, b, 6, 7, d) * gamma);
 
  r[NTT_LENGTH(6)] = barrett_reduce(CALC_D(a, b, 0, 6, d)+
         CALC_D(a, b, 1, 5, d)+
         CALC_D(a, b, 2, 4, d))+d[3]+ 
         montgomery_reduce(d[7]*gamma);
  
  r[NTT_LENGTH(7)] = barrett_reduce(CALC_D(a, b, 0, 7, d)+
         CALC_D(a, b, 1, 6, d))+
         barrett_reduce(CALC_D(a, b, 2, 5, d)+
         CALC_D(a, b, 3, 4, d));
  
#else
#error "NEWHOPE_N must be either 512, 768 or 1024"
#endif
}

#else
#error "USE_SCHOOLBOOK_MULTIPLICATION or USE_KARATSUBA_MULTIPLICATION must be defined."
#endif
