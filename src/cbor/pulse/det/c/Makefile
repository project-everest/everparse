all: extract

CFLAGS += -O3 -I .

EVERPARSE_SRC_PATH = $(realpath ../../../..)
OUTPUT_DIRECTORY:=.

extract: $(OUTPUT_DIRECTORY)/CBORDet.o $(OUTPUT_DIRECTORY)/CBORDetSizeCheck.o $(OUTPUT_DIRECTORY)/CBORDetAbstract.o

test: extract
	+$(MAKE) -C $@

example: extract
	+$(MAKE) -C $@

all-tests: test example

.PHONY: all extract test example all-tests

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

clean-o:
	rm -f *.o

.PHONY: clean-o

clean: test.clean example.clean clean-o clean-extracted

.PHONY: clean

clean-extracted:
	rm -rf extracted

.PHONY: clean-extracted

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
