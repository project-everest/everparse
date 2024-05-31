all: CBOR_Pulse.o
.PHONY: all

EVERCBOR_SRC_PATH = $(realpath ../../../..)
include $(EVERCBOR_SRC_PATH)/karamel.Makefile

CFLAGS += -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<
