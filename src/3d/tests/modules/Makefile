# Standalone hash checker test on a multi-module 3d project: check the
# in-place hashes that EverParse writes into the generated Point.h and
# Point.c. Copied from share/everparse/tests/3d/{,lowstar/}modules, which
# perform the same check with 3d itself.

all: hashchk-check

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
EVERPARSE_API ?= pulse
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --api $(EVERPARSE_API) --fstar $(FSTAR_EXE)

HASHCHK ?= dotnet $(EVERPARSE_HOME)/src/3d/hashchk/bin/Debug/net10.0/win-x64/everparse-hashchk.dll

EVERPARSE_OUTPUT_DIR=obj.$(EVERPARSE_API)
EVERPARSE_INPUT_DIR=src

everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

$(everparse_makefile): $(wildcard src/*.3d) Makefile $(EVERPARSE_HOME)/bin/3d.exe | $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ src/Test.3d

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

build: $(EVERPARSE_ALL_H_FILES)

# Under --api pulse, $(EVERPARSE_ALL_H_FILES) waits for the generated .c
# files too (see src/3d/GenMakefile.fst), hence Point.c is ready here.
hashchk-check: build
	$(HASHCHK) --api $(EVERPARSE_API) --check_inplace_hash src/Point.3d=$(EVERPARSE_OUTPUT_DIR)/Point.h
	$(HASHCHK) --api $(EVERPARSE_API) --check_inplace_hash src/Point.3d=$(EVERPARSE_OUTPUT_DIR)/Point.c

clean:
	rm -rf obj.*

.PHONY: all build clean hashchk-check
