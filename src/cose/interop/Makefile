EVERPARSE_SRC_PATH = $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

OBJFILES = ../snapshot/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c

.PHONY: test
test: signtest verifytest .venv
	./.venv/bin/python test.py

.venv:
	python3 -m venv $@
	$@/bin/pip install pycose

SANFLAGS += -fsanitize=address -fsanitize=undefined
CFLAGS += $(SANFLAGS)
LDFLAGS += $(SANFLAGS)
LDFLAGS += -lssl -lcrypto
CFLAGS += -O0 -g
CFLAGS += -I ../snapshot -I ../../cbor/pulse/det/c

HEADERDEPS = ../snapshot/COSE_Format.h ../../cbor/pulse/det/c/CBORDet.h

common.o: common.c $(HEADERDEPS)
signtest.o: signtest.c $(HEADERDEPS)
verifytest.o: verifytest.c $(HEADERDEPS)
CBOR_Det.o: ../../cbor/pulse/det/c/CBORDet.c $(HEADERDEPS)
COSE_Format.o: ../snapshot/COSE_Format.c $(HEADERDEPS)
	$(CC) $(CFLAGS) -c $< -o $@

signtest: signtest.o common.o COSE_Format.o CBOR_Det.o
verifytest: verifytest.o common.o COSE_Format.o CBOR_Det.o
	$(CC) $(LDFLAGS) $+ -o $@
