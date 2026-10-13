all: extract

CFLAGS += -O3 -I .

EVERPARSE_HOME = $(realpath ../../../../..)
EVERPARSE_LIB_PATH = $(EVERPARSE_HOME)/lib/everparse

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
