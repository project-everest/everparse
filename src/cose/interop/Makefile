EVERPARSE_SRC_PATH = $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

OBJFILES = ../snapshot/COSE_Format.o ../../cbor/pulse/det/c/CBORDet.o

.PHONY: test
test: signtest verifytest .venv
	./.venv/bin/python test.py

.venv:
	python3 -m venv $@
	$@/bin/pip install pycose

CFLAGS += -fsanitize=address -fsanitize=undefined
CFLAGS += -lssl -lcrypto
CFLAGS += -O0 -g
CFLAGS += -I ../snapshot -I ../../cbor/pulse/det/c

signtest: signtest.c common.c ../snapshot/COSE_Format.h $(OBJFILES)
	$(CC)  $(CFLAGS) $(OBJFILES) $< -o $@

verifytest: verifytest.c common.c ../snapshot/COSE_Format.h $(OBJFILES)
	$(CC)  $(CFLAGS) $(OBJFILES) $< -o $@