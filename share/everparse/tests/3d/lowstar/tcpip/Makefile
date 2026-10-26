EVERPARSE_HOME ?= $(realpath ../../../../../..)
include $(EVERPARSE_HOME)/lib/everparse/windows.Makefile
export EVERPARSE_HOME
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_API ?= lowstar
export EVERPARSE_API
EVERPARSE_C_RUNTIME = $(EVERPARSE_HOME)/lib/everparse/3d/krml/lowstar
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/everparse-3d.exe --api $(EVERPARSE_API) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")
SOURCE_FILES_NO_EXTERN=TCP.3d Ethernet.3d
SOURCE_FILES_EXTERN=ICMP.3d IPV4.3d VXLAN.3d UDP.3d IPV6.3d
SOURCE_FILES=$(SOURCE_FILES_NO_EXTERN) $(SOURCE_FILES_EXTERN)

all: interpret extern

interpret: $(SOURCE_FILES) interpret.out
	$(EVERPARSE_CMD) --batch $(SOURCE_FILES) --odir interpret.out
	+$(MAKE) -C interpret.out/ -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-type-limits -Wno-ignored-qualifiers -I $(EVERPARSE_HOME)/lib/everparse/3d -I $(EVERPARSE_C_RUNTIME)/buffer'

extern: $(SOURCE_FILES_EXTERN) extern.out
	$(EVERPARSE_CMD) --input_stream extern --input_stream_include EverParseStream.h --batch $(SOURCE_FILES_EXTERN) --odir extern.out
	+$(MAKE) -C extern.out/ -f Makefile.basic USER_TARGET=test USER_CFLAGS='-I ../extern -Wno-type-limits -Wno-ignored-qualifiers -I $(EVERPARSE_HOME)/lib/everparse/3d -I $(EVERPARSE_C_RUNTIME)/extern'

%.out:
	mkdir -p $@

.PHONY: all interpret extern clean


INCLUDES=$(EVERPARSE_HOME)/lib/everparse/3d $(EVERPARSE_HOME)/lib/everparse/lowparse

FSTAR_OPTIONS += $(addprefix --include , $(INCLUDES))

%.fst-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf interpret.out extern.out
