EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME
FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)
SOURCE_FILES_NO_EXTERN=TCP.3d Ethernet.3d
SOURCE_FILES_EXTERN=ICMP.3d IPV4.3d VXLAN.3d UDP.3d IPV6.3d
SOURCE_FILES=$(SOURCE_FILES_NO_EXTERN) $(SOURCE_FILES_EXTERN)

all: interpret extern

interpret: $(SOURCE_FILES) interpret.out
	$(EVERPARSE_CMD) --batch $(SOURCE_FILES) --odir interpret.out
	+$(MAKE) -C interpret.out/ -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-type-limits -Wno-ignored-qualifiers -I $(EVERPARSE_HOME)/src/3d -I $(EVERPARSE_HOME)/src/3d/prelude/buffer'

extern: $(SOURCE_FILES_EXTERN) extern.out
	$(EVERPARSE_CMD) --input_stream extern --input_stream_include EverParseStream.h --batch $(SOURCE_FILES_EXTERN) --odir extern.out
	+$(MAKE) -C extern.out/ -f Makefile.basic USER_TARGET=test USER_CFLAGS='-I ../extern -Wno-type-limits -Wno-ignored-qualifiers -I $(EVERPARSE_HOME)/src/3d -I $(EVERPARSE_HOME)/src/3d/prelude/extern'

%.out:
	mkdir -p $@

.PHONY: all interpret extern clean

INCLUDES=$(EVERPARSE_HOME)/src/3d/prelude $(EVERPARSE_HOME)/src/3d/prelude/buffer $(EVERPARSE_HOME)/src/lowparse $(KRML_HOME)/krmllib/obj $(KRML_HOME)/krmllib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf interpret.out extern.out
