all: extract

.PHONY: all

CFLAGS += -O3 -I . -Wall

EVERPARSE_SRC_PATH = $(realpath ../../../..)
OUTPUT_DIRECTORY:=.

extract: $(OUTPUT_DIRECTORY)/CBORNondet.o

.PHONY: extract

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

all-tests: test

.PHONY: all-tests

test: extract
	+$(MAKE) -C $@

.PHONY: test

clean-o:
	rm -f *.o

.PHONY: clean-o

clean: clean-o test.clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
