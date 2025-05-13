EVERPARSE_SRC_PATH = $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

OBJFILES = ../c/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c

.PHONY: all
all: test run-bench

.PHONY: test
test: signtest verifytest .venv
	./.venv/bin/python test.py

.PHONY: run-bench
run-bench: bench
	./bench

.venv:
	rm -rf $@ $@.tmp
	python3 -m venv $@.tmp
	$@.tmp/bin/python3 -m pip install pycose
	mv $@.tmp $@

# SANFLAGS += -fsanitize=address -fsanitize=undefined
# CFLAGS += $(SANFLAGS)
# LDFLAGS += $(SANFLAGS)
LDFLAGS += -lssl -lcrypto
CFLAGS += -O3
CFLAGS += -I ../c -I ../../cbor/pulse/det/c
CFLAGS += -Wall -Wenum-conversion

HEADERDEPS = ../c/COSE_Format.h ../../cbor/pulse/det/c/CBORDet.h

COSE_OpenSSL.o: COSE_OpenSSL.c $(HEADERDEPS)
common.o: common.c $(HEADERDEPS) COSE_OpenSSL.h
signtest.o: signtest.c $(HEADERDEPS) common.h
verifytest.o: verifytest.c $(HEADERDEPS) common.h
bench.o: bench.c $(HEADERDEPS) common.h

COSE_Format.o: ../c/COSE_Format.c $(HEADERDEPS)

CBOR_Det.o: ../../cbor/pulse/det/c/CBORDet.c $(HEADERDEPS)

%.o:
	$(CC) $(CFLAGS) -c $< -o $@

signtest: signtest.o COSE_OpenSSL.o common.o COSE_Format.o CBOR_Det.o
verifytest: verifytest.o COSE_OpenSSL.o common.o COSE_Format.o CBOR_Det.o
bench: bench.o COSE_OpenSSL.o common.o COSE_Format.o CBOR_Det.o

bench signtest verifytest: %:
	$(CC) $+ $(LDFLAGS) -o $@
