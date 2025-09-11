EVERPARSE_SRC_PATH = $(realpath ../..)

OBJFILES = ../c/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c

.PHONY: all
all: test run-bench

.PHONY: test
test: signtest verifytest ../.venv
	../.venv/bin/python test.py

.PHONY: run-bench
run-bench: bench
	./bench

../.venv:
	$(MAKE) -C $(dir $@) $(notdir $@)

# SANFLAGS += -fsanitize=address -fsanitize=undefined
# CFLAGS += $(SANFLAGS)
# LDFLAGS += $(SANFLAGS)
LDFLAGS += -lssl -lcrypto
CFLAGS += -O3
CFLAGS += -I ../c -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c
CFLAGS += -Wall -Wenum-conversion

HEADERDEPS = ../c/COSE_Format.h ../c/COSE_OpenSSL.h $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.h

common.o: common.c $(HEADERDEPS)
signtest.o: signtest.c $(HEADERDEPS) common.h
verifytest.o: verifytest.c $(HEADERDEPS) common.h
bench.o: bench.c $(HEADERDEPS) common.h

ALL_O_FILES=common.o signtest.o verifytest.o bench.o

$(ALL_O_FILES): %.o:
	$(CC) $(CFLAGS) -c $< -o $@

signtest: signtest.o common.o
verifytest: verifytest.o common.o
bench: bench.o common.o

COSE_FORMAT_O=../c/COSE_Format.o
COSE_OPENSSL_O=../c/COSE_OpenSSL.o
CBOR_DET_O=$(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.o

bench signtest verifytest: %:
	$(CC) $+ $(COSE_OPENSSL_O) $(COSE_FORMAT_O) $(CBOR_DET_O) $(LDFLAGS) -o $@
