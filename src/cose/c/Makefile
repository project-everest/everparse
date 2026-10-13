all: build

EVERPARSE_HOME = $(realpath ../../..)

CFLAGS += -I $(EVERPARSE_HOME)/include/everparse

ALL_C_FILES := $(wildcard *.c)
ALL_O_FILES := $(ALL_C_FILES:.c=.o)

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -c -Wall -o $@ $<

build: $(ALL_O_FILES)

.PHONY: build all

clean:
	rm -f *.o

.PHONY: clean
