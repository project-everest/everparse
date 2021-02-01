QD_HOME ?= ../../..

all:
	$(QD_HOME)/src/3d/3d --batch --no_copy_everparse_h Test.3d
	! test -e EverParse.h
	! test -e Lib.h
	+$(MAKE) -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -Wno-unused-function -I $(QD_HOME)/src/3d'

.PHONY: all
