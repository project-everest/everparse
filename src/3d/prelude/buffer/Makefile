all: extract

EVERPARSE_SRC_PATH := $(realpath ../../..)

FSTAR_OPTIONS := --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'

ALREADY_CACHED := '-EverParse3d.Actions.All,-EverParse3d.InputStream.All,-EverParse3d.InputStream.Buffer,-EverParse3d.Actions.BackendFlag,-EverParse3d.Actions.BackendFlagValue,-EverParse3d.Readable,-EverParse3d.InputBuffer,'

FSTAR_DEP_OPTIONS := --extract 'krml:*,-Prims,-FStar.Tactics'

INCLUDE_PATHS += ..

include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: EverParse.h

EverParse.rsp: $(ALL_KRML_FILES) ../EverParse.rsp
	for f in $(ALL_KRML_FILES) ; do echo $$f ; done > $@.tmp
	while read file ; do grep "^$$file"'$$' $@.tmp > /dev/null || { echo ../$$file >> $@.tmp ; } ; done < ../EverParse.rsp
	mv $@.tmp $@

EverParse.h: EverParse.rsp
	$(KRML_HOME)/krml \
	  -fstar $(FSTAR_EXE) \
	  -skip-compilation \
	  -skip-makefiles \
	  -bundle 'Prims,C.\*,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle 'EverParse3d.Prelude.StaticHeader+EverParse3d.ErrorCode+EverParse3d.InputStream.Buffer.Aux+EverParse3d.CopyBuffer=LowParse.\*,EverParse3d.\*[rename=EverParse,rename-prefix]' \
	  -warn-error -9@4 \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft \
	  -header ../../noheader.txt \
	  -minimal \
	  -add-include 'EverParse:"EverParseEndianness.h"' \
	  -static-header 'EverParse3d.Prelude.StaticHeader,LowParse.Low.Base,EverParse3d.ErrorCode,EverParse3d.InputStream.\*' \
	  -no-prefix LowParse.Slice \
	  -no-prefix LowParse.Low.BoundedInt \
	  -fmicrosoft \
	  -fextern-c \
	  @$^
	test '!' -e EverParse.c
	test '!' -e SHOULDNOTBETHERE.h

.PHONY: all extract clean verify

clean:
	rm -f *.checked *.krml EverParse.h EverParse.rsp .depend *.tmp .depend.tmp *~

