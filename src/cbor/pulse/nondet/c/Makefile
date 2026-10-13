all: extract

.PHONY: all

CFLAGS += -O3 -I . -Wall

EVERPARSE_HOME = $(realpath ../../../../..)
EVERPARSE_LIB_PATH = $(EVERPARSE_HOME)/lib/everparse

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
