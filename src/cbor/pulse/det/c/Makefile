all: extract

EVERPARSE_SRC_PATH = $(realpath ../../../..)
OUTPUT_DIRECTORY:=.

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

extract: $(OUTPUT_DIRECTORY)/CBORDet.o

test: extract
	+$(MAKE) -C $@

.PHONY: all extract test

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<
