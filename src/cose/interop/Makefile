EVERPARSE_SRC_PATH = $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

OBJFILES = ../snapshot/COSE_Format.o ../../cbor/pulse/det/c/CBORDet.o

.PHONY: test
test: signtest .venv
	./.venv/bin/python test.py

.venv:
	python3 -m venv $@
	$@/bin/pip install pycose

CFLAGS += -fsanitize=address -fsanitize=undefined

signtest: signtest.c ../snapshot/COSE_Format.h $(OBJFILES)
	$(CC) -O2 -g $(CFLAGS) -I ../snapshot -I ../../cbor/pulse/det/c -lssl -lcrypto $(OBJFILES) $< -o $@
