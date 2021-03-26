QD_HOME ?= $(realpath ../../../..)
export QD_HOME

all: all0

EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/src/3d/3d
EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src
EVERPARSE_MAKEFILE=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile
CFLAGS += -I src

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

$(EVERPARSE_MAKEFILE): $(wildcard src/*.3d) $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ src/Test.3d

include $(EVERPARSE_MAKEFILE)

ci: $(EVERPARSE_ALL_O_FILES)
	! test -e $(EVERPARSE_OUTPUT_DIR)/EverParse.h
	! test -e $(EVERPARSE_OUTPUT_DIR)/Lib.h
	$(EVERPARSE_CMD) --check_inplace_hash src/Point.3d=$(EVERPARSE_OUTPUT_DIR)/Point.h
	$(EVERPARSE_CMD) --check_inplace_hash src/Point.3d=$(EVERPARSE_OUTPUT_DIR)/Point.c

ALL_O_FILES=$(EVERPARSE_ALL_O_FILES) $(EVERPARSE_OUTPUT_DIR)/main.o

$(EVERPARSE_OUTPUT_DIR)/main.o: $(EVERPARSE_INPUT_DIR)/main.c $(EVERPARSE_OUTPUT_DIR)/TestWrapper.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_OUTPUT_DIR) -I $(EVERPARSE_HOME)/src/3d -c -o $@ $<

$(EVERPARSE_OUTPUT_DIR)/test.exe: $(ALL_O_FILES)
	$(CC) $(LDFLAGS) -o $@ $^

test: $(EVERPARSE_OUTPUT_DIR)/test.exe
	$<

all0: ci test

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all all0 test clean ci
