QD_HOME ?= $(realpath ../../../..)
export QD_HOME

all: test

EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/src/3d/3d
EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src
EVERPARSE_MAKEFILE=obj/EverParse.Makefile
CFLAGS += -I src

obj:
	mkdir -p $@

$(EVERPARSE_MAKEFILE): $(wildcard src/*.3d) obj
	$(EVERPARSE_CMD) --makefile gmake --odir obj src/Test.3d

include $(EVERPARSE_MAKEFILE)

test: $(EVERPARSE_ALL_O_FILES)
	! test -e obj/EverParse.h
	! test -e obj/Lib.h
	$(EVERPARSE_CMD) --check_inplace_hash src/Point.3d=obj/Point.h
	$(EVERPARSE_CMD) --check_inplace_hash src/Point.3d=obj/Point.c
	# +$(MAKE) -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -Wno-unused-function -I $(QD_HOME)/src/3d'

clean:
	rm -rf obj

.PHONY: all test clean
