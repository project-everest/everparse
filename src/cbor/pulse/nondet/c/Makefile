all: extract

.PHONY: all

CFLAGS += -O3 -I . -Wall

EVERPARSE_SRC_PATH = $(realpath ../../../..)
OUTPUT_DIRECTORY:=.

extract: $(OUTPUT_DIRECTORY)/CBORNondet.o

.PHONY: extract

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

clean-o:
	rm -f *.o

.PHONY: clean-o

clean: clean-o

.PHONY: clean
