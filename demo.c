/*
gcc -Wall -Wextra -g -O3 -fomit-frame-pointer -march=native ./KE/poly.c
./KE/reduce.c ./KE/fips202.c ./KE/verify.c ./KE/cpapke.c ./KE/ntt.c
./KE/precomp.c -DNEWHOPE_N=1024 ./KE/kem.c ./KE/randombytes.c ./ASM_GCM/aes.c
./demo.c miracl.a -o demo -lcrypto -lssl
*/

#include "miracl.h"
#include <inttypes.h>
// #include <math.h>
// #include <stddef.h>
// #include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// Add the hearder file of PKE
#include "./KE/api.h"
#include "./KE/poly.h"
#include "./KE/randombytes.h"
#include "./KE/fips202.h"

// Add the hearder file of ASM GCM
#include "./ASM_GCM/aes.h"

#include "sha31.h"

void hashing_to_big(char *msg, big hash_nb);
void hashing_to_str(char *msg, char *hash_str);
void hashing_display(char *msg_hashed);
void PRF_E(big r_in, big mk, int sec_level, char *r_out);
void PRF_F(int index, char *salt, int sec_level, big f_out);

void NEWHOPE_encrypt_cca(unsigned char *c, unsigned char *ct, unsigned char *m,
                         unsigned char *aad, unsigned char *iv,
                         unsigned char *tag, unsigned char *pk);
void NEWHOPE_decrypt_cca(unsigned char *m, unsigned char *c, unsigned char *ct,
                         unsigned char *aad, unsigned char *iv,
                         unsigned char *tag, unsigned char *sk);

// Convert seconds to milliseconds
#define SEC_TO_MS(sec) ((sec)*1000)
// Convert seconds to microseconds
#define SEC_TO_US(sec) ((sec)*1000000)
// Convert seconds to nanoseconds
#define SEC_TO_NS(sec) ((sec)*1000000000)

// Convert nanoseconds to seconds
#define NS_TO_SEC(ns) ((ns) / 1000000000)
// Convert nanoseconds to milliseconds
#define NS_TO_MS(ns) ((ns) / 1000000)
// Convert nanoseconds to microseconds
#define NS_TO_US(ns) ((ns) / 1000)

uint64_t millis();
uint64_t micros();
uint64_t nanos();

#define Z 50
#define L 500         // Save local storage in demo
#define DATA_SIZE 500 // size of a single data item, 500 or 1000
#define I_PAD 0x36    // for HMAC definition
#define O_PAD 0x5C    // for HMAC definition
#define MR_HASH_BYTES 32
#define SLEVEL 256

typedef struct curve {
  char *A;
  char *B;
  char *P;
  char *Q;
  char *X;
  char *Y;
  int sec_level;
} Curve;

// int main(int argc, char **argv) {
int main() {

  // Get Curve
  Curve curve = {
      .A = "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
           "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc",
      .B = "0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e"
           "156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00",
      .P = "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
           "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      .Q = "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
           "a51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409",
      .X = "00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3db"
           "aa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",
      .Y = "011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662"
           "c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",
      .sec_level = 256};

  uint64_t t_start, t_end, t_tmp1, t_tmp2;

  // Get data from file
  FILE *fp;
  char *line = NULL;
  size_t len = DATA_SIZE;
  ssize_t read;

  char **bigdata = (char **)malloc(L * sizeof(char *));
  int pos = 0;

  fp = fopen("./bigdata_0_5KB.txt", "r");
  if (fp == NULL)
    exit(EXIT_FAILURE);

  while ((read = getline(&line, &len, fp)) != -1) {
    bigdata[pos] = (char *)malloc(DATA_SIZE * sizeof(char));
    strncpy(bigdata[pos], line, DATA_SIZE);
    pos += 1;
  }

  fclose(fp);
  if (line)
    free(line);

  // Data relevant Key generation
  big a, b, p, q, x, y, mk, k, kp, od; // Check if all are used
  epoint *g, *w;

  mirsys(SLEVEL, 16);
  /* initialise system to base 16, curve.sec_level digits per "big" */

  a = mirvar(0);
  b = mirvar(0);
  p = mirvar(0);
  q = mirvar(0);
  x = mirvar(0);
  y = mirvar(0);
  mk = mirvar(0);
  k = mirvar(0);
  kp = mirvar(0);
  od = mirvar(0);
  expint(2, SLEVEL, od);

  instr(a, curve.A);
  instr(b, curve.B);
  instr(p, curve.P);
  instr(q, curve.Q);
  instr(x, curve.X);
  instr(y, curve.Y);

  time_t seed;
  time(&seed);
  irand((unsigned long)seed);

  ecurve_init(a, b, p, MR_PROJECTIVE); // initialise curve

  g = epoint_init(); // base point
  w = epoint_init(); // infinity point

  if (!epoint_set(x, y, 0, g)) // initialise point of order q
  {
    printf("Point (x,y) is not on the curve\n");
    exit(EXIT_FAILURE);
  }
  ecurve_mult(q, g, w);
  if (!point_at_infinity(w)) {
    printf("Point (x,y) is not of order q\n");
    exit(EXIT_FAILURE);
  }

  prepare_monty(q);
  bigrand(od, mk);
  bigrand(q, k);
  bigrand(od, kp);

  printf("==========================================\n");
  printf("size parameters:\nz: %d\n", Z);
  printf("first authentication factor - key mk:\n");
  otnum(mk, stdout);
  printf("second authentication factor - key K:\n");
  otnum(k, stdout);
  printf("second authentication factor - key K':\n");
  otnum(kp, stdout);
  printf("==========================================\n\n");

  // PKE preparation
  unsigned char pk[CRYPTO_PUBLICKEYBYTES];
  unsigned char sk[CRYPTO_SECRETKEYBYTES];
  crypto_kem_keypair(pk, sk);

  // ASM GCM preparation
  unsigned char iv[16];
  randombytes(iv, sizeof(iv));
  unsigned char aad[16]; // This can be called zero or more times as required
  unsigned char gcm_tag[CRYPTO_PUBLICKEYBYTES];

  printf("==========================================\n");
  printf("Public key of PKE:\n");
  hashing_display((char *)pk);
  printf("Secret key of PKE:\n");
  hashing_display((char *)sk);
  printf("IV of ASM GCM:\n");
  hashing_display((char *)iv);
  printf("==========================================\n\n");

  // KE preparation
  unsigned char pk2[CRYPTO_PUBLICKEYBYTES];
  unsigned char sk2[CRYPTO_SECRETKEYBYTES];
  crypto_kem_keypair(pk2, sk2);

  printf("==========================================\n");
  printf("Public key of KE:\n");
  hashing_display((char *)pk2);
  printf("Secret key of KE:\n");
  hashing_display((char *)sk2);
  printf("==========================================\n\n");

  // Tag generation
  big tag[L];
  big tmp_f;
  tmp_f = mirvar(0);
  char kp_str[SLEVEL];

  for (int i = 0; i < L; i++) {
    tag[i] = mirvar(0);
    hashing_to_big(bigdata[i], tag[i]);
    nres_modmult(k, tag[i], tag[i]);
    otstr(kp, kp_str);
    PRF_F(i, kp_str, SLEVEL, tmp_f);
    nres_modadd(tmp_f, tag[i], tag[i]);
  }

  mirkill(tmp_f);

  printf("[v] Tag generation completed\n");

  // IoT operation (Part 1)

  t_start = micros();

  // First message generation
  int index_is_used[L] = {0};
  int index, len_r, Ic[Z];
  for (int i = 0; i < Z; i++) {
    index = rand() % L;
    while (index_is_used[index] == 1) {
      index = rand() % L;
    }
    Ic[i] = index;
    index_is_used[index] = 1;
  }

  big rc;
  rc = mirvar(0);
  bigrand(od, rc);

  char rc_str[SLEVEL];
  len_r = big_to_bytes(SLEVEL, rc, rc_str, FALSE);
  // printf("Plaintext:\n");
  // hashing_display(rc_str);

  // Encrypt rc
  t_tmp1 = micros();
  unsigned char c[CRYPTO_CIPHERTEXTBYTES];
  unsigned char ct[CRYPTO_CIPHERTEXTBYTES];
  NEWHOPE_encrypt_cca(c, ct, (unsigned char *)rc_str, aad, iv, gcm_tag, pk);
  t_tmp2 = micros();
  printf("[-->] %" PRIu64 " microsecond | Encryption on IoT device (part 1)\n",
         (t_tmp2 - t_tmp1));

  // KE

  // Generate M1
  char m1c[1000];
  char m1chashed[MR_HASH_BYTES + 1];
  char msg_tmp[SLEVEL];

  m1c[0] = '\0';
  otstr(mk, msg_tmp);
  strcat(m1c, msg_tmp);
  strcat(m1c, rc_str);
  for (int i = 0; i < Z; i++) {
    sprintf(msg_tmp, "%d", Ic[i]);
    strcat(m1c, msg_tmp);
  }
  strcat(m1c, (char *)c);
  strcat(m1c, (char *)ct);
  strcat(m1c, (char *)pk2);

  hashing_to_str(m1c, m1chashed);
  printf("[v] First message generation completed\n");

  t_end = micros();
  printf("[-->] %" PRIu64 " microsecond | Time of IoT device (part 1)\n",
         (t_end - t_start));

  // Server operation (Part 1)

  t_start = micros();

  // First message vef
  // Decrypt rs
  t_tmp1 = micros();
  char rs_str[SLEVEL];
  NEWHOPE_decrypt_cca((unsigned char *)rs_str, c, ct, aad, iv, gcm_tag, sk);
  t_tmp2 = micros();
  printf("[-->] %" PRIu64 " microsecond | Decryption on server (part 1)\n",
         (t_tmp2 - t_tmp1));
  // printf("Decrypt rs\n");
  // hashing_display(rs_str);

  char m1s[1000];
  char m1shashed[MR_HASH_BYTES + 1];

  m1c[0] = '\0';
  otstr(mk, msg_tmp);
  strcat(m1s, msg_tmp);
  strcat(m1s, rs_str);
  for (int i = 0; i < Z; i++) {
    sprintf(msg_tmp, "%d", Ic[i]);
    strcat(m1s, msg_tmp);
  }
  strcat(m1s, (char *)c);
  strcat(m1s, (char *)ct);
  strcat(m1s, (char *)pk2);

  hashing_to_str(m1s, m1shashed);

  if (strcmp(m1chashed, m1shashed) != 0) {
    printf("[x] First message verification failed\n");
    exit(EXIT_FAILURE);
  } else {
    printf("[v] First message verification completed\n");
  }

  // Framework process
  int Is[Z];
  for (int i = 0; i < Z; i++) {
    index = rand() % L;
    while (index_is_used[index] == 1) {
      index = rand() % L;
    }
    Is[i] = index;
    index_is_used[index] = 1;
  }

  big rs, d_hashed, tmp_f_in_xy, sumx, sumy;
  rs = mirvar(0);
  d_hashed = mirvar(0);
  tmp_f_in_xy = mirvar(0);
  sumx = mirvar(0);
  sumy = mirvar(0);

  bytes_to_big(len_r, rs_str, rs);
  char rps[MR_HASH_BYTES];
  PRF_E(rs, mk, SLEVEL, rps);

  for (int i = 0; i < Z; i++) {
    // X for Ic
    hashing_to_big(bigdata[Ic[i]], d_hashed);
    PRF_F(Ic[i], rps, SLEVEL, tmp_f_in_xy);
    nres_modmult(d_hashed, tmp_f_in_xy, d_hashed);
    nres_modadd(d_hashed, sumx, sumx);

    // Y for Ic
    nres_modmult(tag[Ic[i]], tmp_f_in_xy, tmp_f_in_xy);
    nres_modadd(tmp_f_in_xy, sumy, sumy);

    // X for Is
    hashing_to_big(bigdata[Is[i]], d_hashed);
    PRF_F(Is[i], rps, SLEVEL, tmp_f_in_xy);
    nres_modmult(d_hashed, tmp_f_in_xy, d_hashed);
    nres_modadd(d_hashed, sumx, sumx);

    // Y for Is
    nres_modmult(tag[Is[i]], tmp_f_in_xy, tmp_f_in_xy);
    nres_modadd(tmp_f_in_xy, sumy, sumy);
  }

  nres_modmult(k, sumx, sumx);

  // KE
  t_tmp1 = micros();
  unsigned char ct2[CRYPTO_CIPHERTEXTBYTES];
  unsigned char sss2[CRYPTO_BYTES];
  crypto_kem_enc(ct2, sss2, pk2);
  t_tmp2 = micros();
  printf("[-->] %" PRIu64 " microsecond | KE on server (part 1)\n",
         (t_tmp2 - t_tmp1));

  // Generate M2
  char m2s[1000];
  char m2shashed[MR_HASH_BYTES + 1];

  m2s[0] = '\0';
  strcat(m2s, rs_str);
  for (int i = 0; i < Z; i++) {
    sprintf(msg_tmp, "%d", Is[i]);
    strcat(m2s, msg_tmp);
  }

  otstr(sumx, msg_tmp);
  strcat(m2s, msg_tmp);
  otstr(sumy, msg_tmp);
  strcat(m2s, msg_tmp);
  strcat(m2s, (char *)ct2);
  // strcat(m2s, m1chashed);

  hashing_to_str(m2s, m2shashed);
  printf("[v] Second message generation completed\n");

  t_end = micros();
  printf("[-->] %" PRIu64 " microsecond | Time of server (part 1)\n",
         (t_end - t_start));

  mirkill(rs);
  mirkill(d_hashed);
  mirkill(tmp_f_in_xy);

  // IoT operation (Part 2)

  t_start = micros();

  // Second message vef
  char rpc[MR_HASH_BYTES];
  PRF_E(rc, mk, SLEVEL, rpc);

  big tmp_f_in_c_1, tmp_f_in_c_2, yp;
  tmp_f_in_c_1 = mirvar(0);
  tmp_f_in_c_2 = mirvar(0);
  yp = mirvar(0);

  otstr(kp, kp_str);

  for (int i = 0; i < Z; i++) {
    // for Ic
    PRF_F(Ic[i], rpc, SLEVEL, tmp_f_in_c_1);
    PRF_F(Ic[i], kp_str, SLEVEL, tmp_f_in_c_2);
    nres_modmult(tmp_f_in_c_1, tmp_f_in_c_2, tmp_f_in_c_2);
    nres_modadd(tmp_f_in_c_2, yp, yp);

    // for Is
    PRF_F(Is[i], rpc, SLEVEL, tmp_f_in_c_1);
    PRF_F(Is[i], kp_str, SLEVEL, tmp_f_in_c_2);
    nres_modmult(tmp_f_in_c_1, tmp_f_in_c_2, tmp_f_in_c_2);
    nres_modadd(tmp_f_in_c_2, yp, yp);
  }

  nres_modadd(sumx, yp, yp);

  char m2c[1000];
  char m2chashed[MR_HASH_BYTES + 1];

  m2c[0] = '\0';
  strcat(m2c, rc_str);
  for (int i = 0; i < Z; i++) {
    sprintf(msg_tmp, "%d", Is[i]);
    strcat(m2c, msg_tmp);
  }
  otstr(sumx, msg_tmp);
  strcat(m2c, msg_tmp);
  otstr(yp, msg_tmp);
  strcat(m2c, msg_tmp);
  strcat(m2c, (char *)ct2);
  // strcat(m2c, m1chashed);

  hashing_to_str(m2c, m2chashed);

  if (strcmp(m2shashed, m2chashed) != 0) {
    printf("[x] Second message verification failed\n");
    exit(EXIT_FAILURE);
  } else {
    printf("[v] Second message verification completed\n");
  }

  mirkill(tmp_f_in_c_1);
  mirkill(tmp_f_in_c_2);
  mirkill(sumx);

  // Third message gen

  // KE
  t_tmp1 = micros();
  unsigned char ssc2[CRYPTO_BYTES];
  crypto_kem_dec(ssc2, ct2, sk2);
  t_tmp2 = micros();
  printf("[-->] %" PRIu64 " microsecond | KE on IoT device (part 2)\n",
         (t_tmp2 - t_tmp1));

  char m3c[1000];
  char m3chashed[MR_HASH_BYTES + 1];

  m3c[0] = '\0';
  // strcat(m3c, (char *)ssc2);
  for (int i = 0; i < Z; i++) {
    sprintf(msg_tmp, "%d", Ic[i]);
    strcat(m3c, msg_tmp);
    sprintf(msg_tmp, "%d", Is[i]);
    strcat(m3c, msg_tmp);
  }
  otstr(yp, msg_tmp);
  strcat(m3c, msg_tmp);
  // strcat(m3c, m1chashed);
  // strcat(m3c, m2shashed);

  hashing_to_str(m3c, m3chashed);

  t_end = micros();
  printf("[-->] %" PRIu64 " microsecond | Time of IoT device (part 2)\n",
         (t_end - t_start));

  // session key on c
  printf("[:-)] Client's session key generation completed\n");

  mirkill(rc);

  // Server operation (Part 2)
  t_start = micros();

  // server
  char m3s[1000];
  char m3shashed[MR_HASH_BYTES + 1];

  m3s[0] = '\0';
  // strcat(m3s, (char *)sss2);
  for (int i = 0; i < Z; i++) {
    sprintf(msg_tmp, "%d", Ic[i]);
    strcat(m3s, msg_tmp);
    sprintf(msg_tmp, "%d", Is[i]);
    strcat(m3s, msg_tmp);
  }
  otstr(sumy, msg_tmp);
  strcat(m3s, msg_tmp);
  // strcat(m3s, m1chashed);
  // strcat(m3s, m2shashed);

  hashing_to_str(m3s, m3shashed);

  if (strcmp(m3shashed, m3chashed) != 0) {
    printf("[x] Third message verification failed\n");
    exit(EXIT_FAILURE);
  } else {
    printf("[v] Third message verification completed\n");
  }

  t_end = micros();
  printf("[-->] %" PRIu64 " microsecond | Time of server (part 2)\n",
         (t_end - t_start));

  // session key on c
  printf("[:-)] Server's session key generation completed\n");

  // Free
  for (int i = 0; i < L; i++) {
    free(bigdata[i]);
    mirkill(tag[i]);
  }
  free(bigdata);
  mirkill(sumy);
  mirkill(yp);
  mirkill(a);
  mirkill(b);
  mirkill(p);
  mirkill(q);
  mirkill(x);
  mirkill(y);
  mirkill(mk);
  mirkill(k);
  mirkill(kp);
  mirkill(od);
}

//
//
//
//
//
//
//
//
//
//
//
//
//

void hashing_to_str(char *msg, char *hash_str) {
//  sha256 sh;
//  shs256_init(&sh);
//  for (int i = 0; msg[i] != '\0'; i++) {
//    shs256_process(&sh, msg[i]);
//  }
  sha3_256(hash_str, msg, strlen(msg));
//  shake25633(hash_str, MR_HASH_BYTES, msg, strlen(msg));
  // magic error: output length may pass MR_HASH_BYTES
  if (strlen((char *)hash_str) > MR_HASH_BYTES)
    hash_str[MR_HASH_BYTES] = '\0';
}

void hashing_display(char *msg_hashed) {
  for (size_t i = 0; i < strlen((char *)msg_hashed); i++) {
    printf("%02x", (unsigned char)msg_hashed[i]);
  }
  printf("\n");
}

void hashing_to_big(char *msg, big hash_nb) {
  char res[MR_HASH_BYTES + 1];
  hashing_to_str(msg, res);
  bytes_to_big(MR_HASH_BYTES, (char *)res, hash_nb);
}

// HMAC(H, K) == H(K ^ opad, H(K ^ ipad, text))
void PRF_E(big r_in, big mk, int sec_level, char *r_out) {
  uint8_t mk_str[sec_level];
  uint8_t long_str[sec_level];
  uint8_t res_hash[MR_HASH_BYTES + 1];
  uint8_t r_in_str[sec_level];

  otstr(mk, (char *)mk_str);
  // if the mk is bigger than the buffer size MR_HASH_BYTES
  // aaply the hash function to it and use the result
  if (strlen((char *)mk_str) > MR_HASH_BYTES) {
    hashing_to_str((char *)mk_str, (char *)mk_str);
  }

  size_t len_mk = strlen((char *)mk_str);

  for (size_t i = 0; i < len_mk; i++)
    res_hash[i] = I_PAD ^ mk_str[i];
  if (len_mk < (size_t)MR_HASH_BYTES)
    for (size_t i = len_mk; i < MR_HASH_BYTES; i++)
      res_hash[i] = I_PAD ^ 0;
  res_hash[MR_HASH_BYTES] = '\0';

  strcpy((char *)long_str, (char *)res_hash);
  otstr(r_in, (char *)r_in_str);
  strcat((char *)long_str, (char *)r_in_str);
  hashing_to_str((char *)long_str, (char *)r_in_str);

  for (size_t i = 0; i < len_mk; i++)
    res_hash[i] = O_PAD ^ mk_str[i];
  if (len_mk < (size_t)MR_HASH_BYTES)
    for (size_t i = len_mk; i < MR_HASH_BYTES; i++)
      res_hash[i] = O_PAD ^ 0;
  res_hash[MR_HASH_BYTES] = '\0';

  memset(long_str, 0, sizeof(long_str));
  strcpy((char *)long_str, (char *)res_hash);
  strcat((char *)long_str, (char *)r_in_str);
  hashing_to_str((char *)long_str, r_out);
}

void PRF_F(int index, char *salt, int sec_level, big f_out) {
  uint8_t salt_str[MR_HASH_BYTES + 1];
  uint8_t long_str[sec_level];
  uint8_t res_hash[MR_HASH_BYTES + 1];
  uint8_t index_str[MR_HASH_BYTES + 1];

  // if the salt is bigger than the buffer size MR_HASH_BYTES
  // aaply the hash function to it and use the result
  if (strlen(salt) >= MR_HASH_BYTES) {
    hashing_to_str(salt, (char *)salt_str);
  } else {
    strcpy((char *)salt_str, salt);
    salt_str[strlen(salt)] = '\0';
  }
  size_t len_salt = strlen((char *)salt_str);

  for (size_t i = 0; i < len_salt; i++)
    res_hash[i] = I_PAD ^ salt_str[i];
  if (len_salt < (size_t)MR_HASH_BYTES)
    for (size_t i = len_salt; i < MR_HASH_BYTES; i++)
      res_hash[i] = I_PAD ^ 0;
  res_hash[MR_HASH_BYTES] = '\0';

  sprintf((char *)index_str, "%d", index);
  strcpy((char *)long_str, (char *)res_hash);
  strcat((char *)long_str, (char *)index_str);
  hashing_to_str((char *)long_str, (char *)index_str);

  for (size_t i = 0; i < len_salt; i++)
    res_hash[i] = O_PAD ^ salt_str[i];
  if (len_salt < (size_t)MR_HASH_BYTES)
    for (size_t i = len_salt; i < MR_HASH_BYTES; i++)
      res_hash[i] = O_PAD ^ 0;
  res_hash[MR_HASH_BYTES] = '\0';

  memset(long_str, 0, sizeof(long_str));
  strcpy((char *)long_str, (char *)res_hash);
  strcat((char *)long_str, (char *)index_str);
  hashing_to_big((char *)long_str, f_out);
}

// Get a time stamp in milliseconds.
uint64_t millis() {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  uint64_t ms = SEC_TO_MS((uint64_t)ts.tv_sec) + NS_TO_MS((uint64_t)ts.tv_nsec);
  return ms;
}

// Get a time stamp in microseconds.
uint64_t micros() {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  uint64_t us = SEC_TO_US((uint64_t)ts.tv_sec) + NS_TO_US((uint64_t)ts.tv_nsec);
  return us;
}

// Get a time stamp in nanoseconds.
uint64_t nanos() {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  uint64_t ns = SEC_TO_NS((uint64_t)ts.tv_sec) + (uint64_t)ts.tv_nsec;
  return ns;
}

void NEWHOPE_encrypt_cca(unsigned char *c, unsigned char *ct, unsigned char *m,
                         unsigned char *aad, unsigned char *iv,
                         unsigned char *tag, unsigned char *pk) {
  unsigned char ssc[CRYPTO_BYTES];
  crypto_kem_enc(ct, ssc, pk);

  // implemente ACM GCM
  encrypt(m, strlen((char *)m), aad, strlen((char *)add), ssc, iv, c, tag);
}

void NEWHOPE_decrypt_cca(unsigned char *m, unsigned char *c, unsigned char *ct,
                         unsigned char *aad, unsigned char *iv,
                         unsigned char *tag, unsigned char *sk) {
  unsigned char sss[CRYPTO_BYTES];
  crypto_kem_dec(sss, ct, sk);

  // implemente ACM GCM
  decrypt(c, strlen((char *)c), aad, strlen((char *)aad), tag, sss, iv, m);
}
