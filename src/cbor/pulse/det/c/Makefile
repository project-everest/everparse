all: extract

CFLAGS += -O3 -I .

EVERPARSE_SRC_PATH = $(realpath ../../../..)
OUTPUT_DIRECTORY:=.

extract: $(OUTPUT_DIRECTORY)/CBORDet.o $(OUTPUT_DIRECTORY)/CBORDetSizeCheck.o $(OUTPUT_DIRECTORY)/CBORDetAbstract.o

test: extract
	+$(MAKE) -C $@

.PHONY: all extract test

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<
