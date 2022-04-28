#ifndef NTT_H
#define NTT_H

#include "inttypes.h"

void ntt(int16_t *poly, const int16_t *gammas);
void invntt(int16_t *poly, const int16_t *gammas);
void basemul(int16_t *r, const int16_t *a, const int16_t *b, int16_t gamma);

#endif
