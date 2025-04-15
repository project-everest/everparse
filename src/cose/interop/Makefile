EVERPARSE_SRC_PATH = $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

OBJFILES = ../snapshot/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c

.PHONY: all
all: test run-bench

.PHONY: test
test: signtest verifytest .venv
	./.venv/bin/python test.py

.PHONY: run-bench
run-bench: bench
	./bench

.venv:
	python3 -m venv $@
	$@/bin/pip install pycose

# SANFLAGS += -fsanitize=address -fsanitize=undefined
# CFLAGS += $(SANFLAGS)
# LDFLAGS += $(SANFLAGS)
LDFLAGS += -lssl -lcrypto
CFLAGS += -O3
CFLAGS += -I ../snapshot -I ../../cbor/pulse/det/c
CFLAGS += -Wall -Wenum-conversion

HEADERDEPS = ../snapshot/COSE_Format.h ../../cbor/pulse/det/c/CBORDet.h

common.o: common.c $(HEADERDEPS)
signtest.o: signtest.c $(HEADERDEPS) common.h
verifytest.o: verifytest.c $(HEADERDEPS) common.h
bench.o: bench.c $(HEADERDEPS) common.h
	$(CC) $(CFLAGS) -c $< -o $@

COSE_Format.o: ../snapshot/COSE_Format.c $(HEADERDEPS)
	$(CC) $(CFLAGS) -c $< -o $@

CBOR_Det.o: ../../cbor/pulse/det/c/CBORDet.c $(HEADERDEPS)
	$(CC) $(CFLAGS) -c $< -o $@

signtest: signtest.o common.o COSE_Format.o CBOR_Det.o
verifytest: verifytest.o common.o COSE_Format.o CBOR_Det.o
bench: bench.o common.o COSE_Format.o CBOR_Det.o
	$(CC) $(LDFLAGS) $+ -o $@
