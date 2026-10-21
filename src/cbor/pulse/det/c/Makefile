all: extract

EVERPARSE_HOME = $(realpath ../../../../..)
EVERPARSE_LIB_PATH = $(EVERPARSE_HOME)/lib/everparse
EVERPARSE_INCLUDE_PATH = $(EVERPARSE_HOME)/include/everparse

# -I . for the internal/ headers, which stay next to the sources; the public
# headers live in $(EVERPARSE_INCLUDE_PATH), and internal/ refers to them as
# <everparse/CBORDet.h>, hence its parent directory too.
CFLAGS += -O3 -I . -I $(EVERPARSE_HOME)/include -I $(EVERPARSE_INCLUDE_PATH)

extract: $(EVERPARSE_LIB_PATH)/CBORDet.o

$(EVERPARSE_LIB_PATH)/CBORDet.o: CBORDet.c
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -c -o $@ $<

test: extract
	+$(MAKE) -C $@

example: extract
	+$(MAKE) -C $@

all-tests: test example

.PHONY: all extract test example all-tests

clean-o:
	rm -f *.o $(EVERPARSE_LIB_PATH)/CBORDet.o

.PHONY: clean-o

clean: test.clean example.clean clean-o clean-extracted

.PHONY: clean

clean-extracted:
	rm -rf extracted

.PHONY: clean-extracted

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
