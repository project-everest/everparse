all: build

EVERPARSE_SRC_PATH = $(realpath ..)

OUTPUT_DIRECTORY=_output
OUTPUT=$(OUTPUT_DIRECTORY)/COSE.Format.fst

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

CFLAGS += -I snapshot -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

ALL_C_FILES := $(wildcard *.c) $(wildcard snapshot/*.c)
ALL_O_FILES := $(ALL_C_FILES:.c=.o)

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -c -Wall -o $@ $<

build: $(ALL_O_FILES)

.PHONY: build

$(OUTPUT): cose.cddl ../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT))
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

.PHONY: all

test-extract: $(OUTPUT)
	+$(MAKE) -f extract.Makefile test

test: test-extract

.PHONY: test-extract test

# This rule is incompatible with `test-extract`
snapshot: $(OUTPUT)
	+$(MAKE) -f extract.Makefile snapshot

.PHONY: snapshot

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
