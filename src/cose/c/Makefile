all: build

EVERPARSE_SRC_PATH = $(realpath ../..)

CFLAGS += -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

ALL_C_FILES := $(wildcard *.c)
ALL_O_FILES := $(ALL_C_FILES:.c=.o)

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -c -Wall -o $@ $<

build: $(ALL_O_FILES)

.PHONY: build all
