QD_HOME ?= $(realpath ../../../..)
export QD_HOME

all: test

EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/src/3d/3d
EVERPARSE_OUTPUT_DIR=.

EverParse.Makefile: $(wildcard *.3d)
	$(EVERPARSE_CMD) --gnu_makefile Test.3d

-include EverParse.Makefile

test: $(ALL_O_FILES)
	! test -e EverParse.h
	! test -e Lib.h
	# +$(MAKE) -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -Wno-unused-function -I $(QD_HOME)/src/3d'

clean:
	rm -f *.c *.h *.o *.fst* *.rsp EverParse.Makefile *.krml

.PHONY: all test clean
