QD_HOME ?= $(realpath ../../../..)
export QD_HOME

all: test

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

test: $(EVERPARSE_ALL_O_FILES)
	! test -e $(EVERPARSE_OUTPUT_DIR)/EverParse.h
	! test -e $(EVERPARSE_OUTPUT_DIR)/Lib.h
	$(EVERPARSE_CMD) --check_inplace_hash src/Point.3d=$(EVERPARSE_OUTPUT_DIR)/Point.h
	$(EVERPARSE_CMD) --check_inplace_hash src/Point.3d=$(EVERPARSE_OUTPUT_DIR)/Point.c
	# +$(MAKE) -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -Wno-unused-function -I $(QD_HOME)/src/3d'

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all test clean
