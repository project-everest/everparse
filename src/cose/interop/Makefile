EVERPARSE_SRC_PATH = $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

OBJFILES = ../snapshot/COSE_Format.o ../../cbor/pulse/det/c/CBORDet.o

signtest: signtest.c ../snapshot/COSE_Format.h $(OBJFILES)
	$(CC) -O0 -g $(CFLAGS) -I ../snapshot -I ../../cbor/pulse/det/c -lssl -lcrypto $(OBJFILES) $< -o $@