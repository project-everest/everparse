# Test that --save_hashes is honored with --makefile.
# The generated Makefile should produce .json hash files,
# and --check_hashes strong should validate them.

all: check

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)

EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src

everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

# Generate the Makefile with --save_hashes
$(everparse_makefile): $(wildcard src/*.3d) | $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --save_hashes --skip_o_rules --no_copy_everparse_h --makefile_name $@ src/Test.3d src/Test2.3d

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

# Build all generated files including hash .json files
build: $(EVERPARSE_ALL_H_FILES) $(EVERPARSE_ALL_C_FILES) $(EVERPARSE_ALL_JSON_FILES)

# Verify saved hashes with --check_hashes strong
check: build
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --check_hashes strong src/Test.3d src/Test2.3d

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all build check clean
