CC = /usr/bin/gcc
CFLAGS = -Wall -Wextra -g -O3 -fomit-frame-pointer -march=native

HEADERS = params.h poly.h randombytes.h ntt.h reduce.h verify.h cpapke.h
SOURCES = poly.c reduce.c fips202.c verify.c cpapke.c ntt.c precomp.c
KEM  = kem.c

all:	test_kem512 \
	test_kem768 \
	test_kem1024 \
	speed_kem512 \
	speed_kem768 \
	speed_kem1024


test_kem512: $(HEADERS) $(SOURCES) $(KEM) test_nhcompact.c randombytes.c
	$(CC) $(CFLAGS) $(SOURCES) -DNEWHOPE_N=512 $(KEM) randombytes.c test_nhcompact.c -o $@

test_kem768: $(HEADERS) $(SOURCES) $(KEM) test_nhcompact.c randombytes.c
	$(CC) $(CFLAGS) $(SOURCES) -DNEWHOPE_N=768 $(KEM) randombytes.c test_nhcompact.c -o $@

test_kem1024: $(HEADERS) $(SOURCES) $(KEM) test_nhcompact.c randombytes.c
	$(CC) $(CFLAGS) $(SOURCES) -DNEWHOPE_N=1024 $(KEM) randombytes.c test_nhcompact.c -o $@

.PHONY: clean

clean:
	-rm test_kem*
	-rm speed_kem*
