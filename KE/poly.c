#include <string.h>
#include "poly.h"
#include "ntt.h"
#include "reduce.h"
#include "fips202.h"

extern int16_t gammas_bitrev_montgomery[];
extern int16_t gammas_inv_organized_bitrev_montgomery[];

/*************************************************
* Name:        flipabs
*
* Description: Computes |(x mod q) - Q/2|
*
* Arguments:   int16_t x: input coefficient
*
* Returns |(x mod q) - Q/2|
**************************************************/
static uint16_t flipabs(int16_t x)
{
  int16_t r,m;
  
  r = barrett_reduce(x);
  r -= NEWHOPE_Q/2;
  
  m = r >> 15;
  return (r + m) ^ m;
}

/*************************************************
* Name:        poly_frombytes
*
* Description: De-serialization of a polynomial
*
* Arguments:   - poly *r:                pointer to output polynomial
*              - const unsigned char *a: pointer to input byte array
**************************************************/
void poly_frombytes(poly *r, const unsigned char *a)
{
  int i;
  for(i=0;i<NEWHOPE_N/2;i++)
  {
    r->coeffs[2*i+0] =  a[3*i+0]       | (((uint16_t)a[3*i+1] & 0x0f) << 8);
    r->coeffs[2*i+1] = (a[3*i+1] >> 4) | (((uint16_t)a[3*i+2] & 0xff) << 4);
  }
}

/*************************************************
* Name:        poly_tobytes
*
* Description: Serialization of a polynomial
*
* Arguments:   - unsigned char *r: pointer to output byte array
*              - const poly *p:    pointer to input polynomial
**************************************************/
void poly_tobytes(unsigned char *r, const poly *p)
{
  int i;
  uint16_t t0,t1;
  for(i=0;i<NEWHOPE_N/2;i++)
  {
    t0 = barrett_reduce(p->coeffs[2*i+0]);
    t1 = barrett_reduce(p->coeffs[2*i+1]);

    r[3*i+0] =  t0 & 0xff;
    r[3*i+1] = (t0 >> 8) | ((t1 & 0xf) << 4);
    r[3*i+2] = (t1 >> 4);
  }
}

/*************************************************
* Name:        poly_compress
*
* Description: Compression and subsequent serialization of a polynomial
*
* Arguments:   - unsigned char *r: pointer to output byte array
*              - const poly *a:    pointer to input polynomial
**************************************************/
void poly_compress(unsigned char * restrict r, const poly * restrict a)
{
  uint8_t t[8];
  int i,j,k=0;

#if (NEWHOPE_POLYCOMPRESSEDBITS == 3)
  for(i=0;i<NEWHOPE_N;i+=8)
  { 
    for(j=0;j<8;j++)
      t[j] = ((((uint16_t)barrett_reduce(a->coeffs[i+j]) << 3) + NEWHOPE_Q/2) / NEWHOPE_Q) & 7;

    r[k]   =  t[0]       | (t[1] << 3) | (t[2] << 6);
    r[k+1] = (t[2] >> 2) | (t[3] << 1) | (t[4] << 4) | (t[5] << 7);
    r[k+2] = (t[5] >> 1) | (t[6] << 2) | (t[7] << 5);
    k += 3;
  }
#elif (NEWHOPE_POLYCOMPRESSEDBITS == 4)
  for(i=0;i<NEWHOPE_N;i+=8)
  {
    for(j=0;j<8;j++)
      t[j] = ((((uint16_t)barrett_reduce(a->coeffs[i+j]) << 4) + NEWHOPE_Q/2) / NEWHOPE_Q) & 15;

    r[k]   = t[0] | (t[1] << 4);
    r[k+1] = t[2] | (t[3] << 4);
    r[k+2] = t[4] | (t[5] << 4);
    r[k+3] = t[6] | (t[7] << 4);
    k += 4;
  }
#else
#error "NEWHOPE_POLYCOMPRESSEDBITS needs to be in {3, 4}"
#endif
}

/*************************************************
* Name:        poly_decompress
*
* Description: De-serialization and subsequent decompression of a polynomial;
*              approximate inverse of poly_compress
*
* Arguments:   - poly *r:                pointer to output polynomial
*              - const unsigned char *a: pointer to input byte array
**************************************************/
void poly_decompress(poly * restrict r, const unsigned char * restrict a)
{
  int i;
#if (NEWHOPE_POLYCOMPRESSEDBITS == 3)
  for(i=0;i<NEWHOPE_N;i+=8)
  {
    r->coeffs[i+0] =  (((a[0] & 7) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+1] = ((((a[0] >> 3) & 7) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+2] = ((((a[0] >> 6) | ((a[1] << 2) & 4)) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+3] = ((((a[1] >> 1) & 7) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+4] = ((((a[1] >> 4) & 7) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+5] = ((((a[1] >> 7) | ((a[2] << 1) & 6)) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+6] = ((((a[2] >> 2) & 7) * NEWHOPE_Q) + 4) >> 3;
    r->coeffs[i+7] = ((((a[2] >> 5)) * NEWHOPE_Q) + 4) >> 3;
    a += 3;
  }
#elif (NEWHOPE_POLYCOMPRESSEDBITS == 4)
  for(i=0;i<NEWHOPE_N;i+=8)
  {
    r->coeffs[i+0] = (((a[0] & 15) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+1] = (((a[0] >> 4) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+2] = (((a[1] & 15) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+3] = (((a[1] >> 4) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+4] = (((a[2] & 15) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+5] = (((a[2] >> 4) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+6] = (((a[3] & 15) * NEWHOPE_Q) + 8) >> 4;
    r->coeffs[i+7] = (((a[3] >> 4) * NEWHOPE_Q) + 8) >> 4;
    a += 4;
  }
#else
#error "NEWHOPE_POLYCOMPRESSEDBITS needs to be in {3, 4}"
#endif
}

/*************************************************
* Name:        poly_frommsg
*
* Description: Convert 32-byte message to polynomial
*
* Arguments:   - poly *r:                  pointer to output polynomial
*              - const unsigned char *msg: pointer to input message
**************************************************/
void poly_frommsg(poly *r, const unsigned char *msg)
{
  unsigned int i,j,mask;
  for(i=0;i<NEWHOPE_SYMBYTES;i++)
  {
    for(j=0;j<8;j++)
    {
      mask = -((msg[i] >> j)&1);
      r->coeffs[8*i+j+  0] = mask & (NEWHOPE_Q/2);
      r->coeffs[8*i+j+256] = mask & (NEWHOPE_Q/2);
#if   (NEWHOPE_N == 768)
      r->coeffs[8*i+j+512] = mask & (NEWHOPE_Q/2);
#elif (NEWHOPE_N == 1024)
      r->coeffs[8*i+j+512] = mask & (NEWHOPE_Q/2);
      r->coeffs[8*i+j+768] = mask & (NEWHOPE_Q/2);
#endif
    }
  }
}

/*************************************************
* Name:        poly_tomsg
*
* Description: Convert polynomial to 32-byte message
*
* Arguments:   - unsigned char *msg: pointer to output message
*              - const poly *x:      pointer to input polynomial
**************************************************/
void poly_tomsg(unsigned char *msg, const poly *x)
{
  unsigned int i;
  uint16_t t;

  memset(msg,0,NEWHOPE_SYMBYTES);

  for(i=0;i<256;i++)
  {
    t  = flipabs(x->coeffs[i+  0]);
    t += flipabs(x->coeffs[i+256]);
#if   (NEWHOPE_N == 512)    
    t = (t - NEWHOPE_Q/2);
#elif (NEWHOPE_N == 768)
    t += flipabs(x->coeffs[i+512]);
    t = (t - 3*NEWHOPE_Q/4);
#elif (NEWHOPE_N == 1024)
    t += flipabs(x->coeffs[i+512]);
    t += flipabs(x->coeffs[i+768]);
    t = (t - NEWHOPE_Q);
#endif

    t >>= 15;
    msg[i>>3] |= t<<(i&7);
  }
}
 
/*************************************************
* Name:        poly_uniform
*
* Description: Sample a polynomial deterministically from a seed,
*              with output polynomial looking uniformly random
*
* Arguments:   - poly *a:                   pointer to output polynomial
*              - const unsigned char *seed: pointer to input seed
**************************************************/
void poly_uniform(poly *a, const unsigned char *seed)
{
  unsigned int ctr=0;
  uint16_t val;
  uint64_t state[25];
  uint8_t buf[SHAKE128_RATE];
  uint8_t extseed[NEWHOPE_SYMBYTES+1];
  int i,j;

  memcpy(extseed,seed,NEWHOPE_SYMBYTES);

  for(i=0;i<NEWHOPE_N;i+=64) /* generate a in blocks of 64 coefficients */
  {
    ctr = 0;
    extseed[NEWHOPE_SYMBYTES] = i/64; /* domain-separate the 8, 12 or 16 independent calls */
    shake128_absorb(state, extseed, NEWHOPE_SYMBYTES+1);
    while(ctr < 64) /* Very unlikely to run more than once */
    {
      shake128_squeezeblocks(buf,1,state);
      for(j=0;j<SHAKE128_RATE && ctr < 64;j+=2)
      {
        val = (buf[j] | ((uint16_t) buf[j+1] << 8));
#if   (NEWHOPE_N == 512 || NEWHOPE_N == 1024)
        if(val < 19*NEWHOPE_Q)
#elif (NEWHOPE_N == 768)
        if(val < 18*NEWHOPE_Q)      
#endif
        {
          a->coeffs[i+ctr] = val;
          ctr++;
        }
      }
    }
  }
}

/*************************************************
* Name:        poly_sample
*
* Description: Sample a polynomial deterministically from a seed and a nonce,
*              with output polynomial close to centered binomial distribution
*              with parameter k=8
*
* Arguments:   - poly *r:                   pointer to output polynomial
*              - const unsigned char *seed: pointer to input seed
*              - unsigned char nonce:       one-byte input nonce
**************************************************/
void poly_sample(poly *r, const unsigned char *seed, unsigned char nonce)
{
#if NEWHOPE_K != 2
#error "poly_sample in poly.c only supports k=2"
#endif
  unsigned char buf[128], a, b;
  uint32_t t, d;
  int i,j,k;

  unsigned char extseed[NEWHOPE_SYMBYTES+2];

  memcpy(extseed,seed,NEWHOPE_SYMBYTES);
  extseed[NEWHOPE_SYMBYTES] = nonce;

  for(i=0;i<NEWHOPE_N;i+=256) /* Generate noise in blocks of 256 coefficients */
  {
    extseed[NEWHOPE_SYMBYTES+1] = i/256;
    shake256(buf,128,extseed,NEWHOPE_SYMBYTES+2);
    for(j=0;j<128;j+=4)
    {
      t = buf[j] | ((uint32_t)buf[j+1] << 8) | ((uint32_t)buf[j+2] << 16) | ((uint32_t)buf[j+3] << 24);
      d = t & 0x55555555;
      d += (t >> 1) & 0x55555555;
      
      for(k=0;k<8;k++)
      {
        a = (d >>  4*k)    & 0x3;
        b = (d >> (4*k+2)) & 0x3;
        r->coeffs[i+2*j+k] = a - b;
      }
    }
  }
}

/*************************************************
* Name:        poly_basemul
*
* Description: Multiply two polynomials in NTT domain.
*
* Arguments:   - poly *r:       pointer to output polynomial
*              - const poly *a: pointer to first input polynomial
*              - const poly *b: pointer to second input polynomial
**************************************************/
void poly_basemul(poly *r, const poly *a, const poly *b)
{
  int i,k=NEWHOPE_NTT_LENGTH/2;
  for(i=0;i<NEWHOPE_NTT_LENGTH;i+=2) {
    basemul(r->coeffs + i, 
            a->coeffs + i, 
            b->coeffs + i, 
            gammas_bitrev_montgomery[k]);
    
    basemul(r->coeffs + i + 1, 
            a->coeffs + i + 1, 
            b->coeffs + i + 1, 
            -gammas_bitrev_montgomery[k++]); 
  }
}

/*************************************************
* Name:        poly_add
*
* Description: Add two polynomials
*
* Arguments:   - poly *r:       pointer to output polynomial
*              - const poly *a: pointer to first input polynomial
*              - const poly *b: pointer to second input polynomial
**************************************************/
void poly_add(poly *r, const poly *a, const poly *b)
{
  int i;
  for(i=0;i<NEWHOPE_N;i++)
    r->coeffs[i] = (a->coeffs[i] + b->coeffs[i]);
}

/*************************************************
* Name:        poly_sub
*
* Description: Subtract two polynomials
*
* Arguments:   - poly *r:       pointer to output polynomial
*              - const poly *a: pointer to first input polynomial
*              - const poly *b: pointer to second input polynomial
**************************************************/
void poly_sub(poly *r, const poly *a, const poly *b)
{
  int i;
  for(i=0;i<NEWHOPE_N;i++)
    r->coeffs[i] = (a->coeffs[i] - b->coeffs[i]);
}

/*************************************************
* Name:        poly_ntt
*
* Description: Forward NTT transform of a polynomial in place
*              Input is assumed to have coefficients in bitreversed order
*              Output has coefficients in normal order
*
* Arguments:   - poly *r: pointer to in/output polynomial
**************************************************/
void poly_ntt(poly *r)
{
  int i;
  for(i=0;i<NEWHOPE_NTT_POLY;i++)
    ntt(r->coeffs+i*NEWHOPE_NTT_LENGTH, gammas_bitrev_montgomery);
}

/*************************************************
* Name:        poly_invntt
*
* Description: Inverse NTT transform of a polynomial in place
*              Input is assumed to have coefficients in normal order
*              Output has coefficients in normal order
*
* Arguments:   - poly *r: pointer to in/output polynomial
**************************************************/
void poly_invntt(poly *r)
{  
  int i;
  for(i=0;i<NEWHOPE_NTT_POLY;i++)  
    invntt(r->coeffs+i*NEWHOPE_NTT_LENGTH, gammas_inv_organized_bitrev_montgomery);
}

