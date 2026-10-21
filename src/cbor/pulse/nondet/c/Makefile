all: extract

.PHONY: all

EVERPARSE_HOME = $(realpath ../../../../..)
EVERPARSE_LIB_PATH = $(EVERPARSE_HOME)/lib/everparse
EVERPARSE_INCLUDE_PATH = $(EVERPARSE_HOME)/include/everparse

# -I . for the internal/ headers, which stay next to the sources; the public
# headers live in $(EVERPARSE_INCLUDE_PATH), and internal/ refers to them as
# <everparse/CBORNondet.h>, hence its parent directory too.
CFLAGS += -O3 -I . -Wall -I $(EVERPARSE_HOME)/include -I $(EVERPARSE_INCLUDE_PATH)

extract: $(EVERPARSE_LIB_PATH)/CBORNondet.o

.PHONY: extract

$(EVERPARSE_LIB_PATH)/CBORNondet.o: CBORNondet.c
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -c -o $@ $<

all-tests: test example

.PHONY: all-tests

test: extract
	+$(MAKE) -C $@

.PHONY: test

example: extract
	+$(MAKE) -C $@

.PHONY: example

clean-o:
	rm -f *.o $(EVERPARSE_LIB_PATH)/CBORNondet.o

.PHONY: clean-o

clean: clean-o test.clean example.clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
