# Standalone hash checker test on the .json hash files produced by a
# Makefile generated with --save_hashes. Copied from
# share/everparse/tests/3d/{,lowstar/}save_hashes, which perform the same
# check with 3d itself.

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
	$(EVERPARSE_CMD) --makefile gmake --save_hashes --skip_o_rules --no_copy_everparse_h --makefile_name $@ src/Test.3d src/Test2.3d

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

build: $(EVERPARSE_ALL_H_FILES) $(EVERPARSE_ALL_C_FILES) $(EVERPARSE_ALL_JSON_FILES)

hashchk-check: build
	$(HASHCHK) --api $(EVERPARSE_API) --odir $(EVERPARSE_OUTPUT_DIR) --check_hashes strong src/Test.3d src/Test2.3d

clean:
	rm -rf obj.*

.PHONY: all build clean hashchk-check
