# Tests and benchmarks of the verified duplicate map key checks of the
# EverCBOR nondet API (cbor_nondet_parse_bounded_sort,
# cbor_nondet_parse_bounded_hash and the hand-written
# cbor_nondet_parse_bounded_hash_random wrapper, and their *_alloc
# variants allocating their scratch space), against the verified
# reference cbor_nondet_parse_bounded.
#
#   make test        differential tests, no-malloc check (allocation
#                    counting and failure injection for the *_alloc variants)
#   make test-asan   same, with -fsanitize=address,undefined
#   make bench       benchmarks -> bench.csv

EVERPARSE_HOME ?= $(realpath ../../../../..)
NONDET_C ?= $(EVERPARSE_HOME)/src/cbor/pulse/nondet/c

CC ?= cc
OPT ?= -O2
CFLAGS_T = $(OPT) -Wall -Wextra -Werror -std=c11 -Wno-unused-function \
  -I $(EVERPARSE_HOME)/include/everparse
CFLAGS_VER = $(OPT) -w -I $(NONDET_C) -I $(EVERPARSE_HOME)/include \
  -I $(EVERPARSE_HOME)/include/everparse
WRAP = -Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc,--wrap=free

all: test bench

.PHONY: all test test-asan bench clean

out/CBORNondet.o: $(NONDET_C)/CBORNondet.c
	@mkdir -p out
	$(CC) $(CFLAGS_VER) $(EXTRA) -c -o $@ $<

out/%.exe: %.c gen.h out/CBORNondet.o
	$(CC) $(CFLAGS_T) $(EXTRA) -o $@ $< out/CBORNondet.o $(if $(filter test_%,$*),$(WRAP))

test: out/test_dupcheck.exe
	./out/test_dupcheck.exe

test-asan:
	$(MAKE) clean
	ASAN_OPTIONS=allocator_may_return_null=1 $(MAKE) test OPT="-O1 -g" EXTRA="-fsanitize=address,undefined -fno-sanitize-recover=all"
	$(MAKE) clean

bench: out/bench_dupcheck.exe
	./out/bench_dupcheck.exe > bench.csv

clean:
	rm -rf out
