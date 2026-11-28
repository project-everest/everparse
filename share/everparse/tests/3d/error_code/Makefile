# Test for the {:error-code ...} 3D field annotation (--api pulse only).
#
# The C driver in src/main.c checks the exact status returned by the
# validators and passed to the error handler when a field constraint fails.
# The negative-test target checks that 3D rejects invalid annotations.

all: world

########################################################
# Variables needed by the EverParse-generated Makefile #
########################################################

EVERPARSE_HOME ?= $(realpath ../../../../..)
export EVERPARSE_HOME

include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_EXE=$(EVERPARSE_HOME)/bin/everparse-3d.exe $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")

EVERPARSE_OPTIONS=--api pulse

EVERPARSE_CMD=$(EVERPARSE_EXE) $(EVERPARSE_OPTIONS)

EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src

#########################################
# Generating and including the Makefile #
#########################################

everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

$(everparse_makefile): $(EVERPARSE_INPUT_DIR)/Test.3d | $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ $<

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

#############################
# Building the test program #
#############################

all_o_files=$(EVERPARSE_ALL_O_FILES) $(EVERPARSE_OUTPUT_DIR)/main.o

# The wrapper headers include the copied runtime EverParse.h, so it must be
# an explicit prerequisite here to avoid a parallel build race.
$(EVERPARSE_OUTPUT_DIR)/main.o: $(EVERPARSE_INPUT_DIR)/main.c $(EVERPARSE_OUTPUT_DIR)/Test.h $(EVERPARSE_OUTPUT_DIR)/TestWrapper.h $(EVERPARSE_OUTPUT_DIR)/EverParse.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_OUTPUT_DIR) -c -o $@ $<

$(EVERPARSE_OUTPUT_DIR)/test.exe: $(all_o_files)
	$(CC) $(LDFLAGS) -o $@ $^

test: $(EVERPARSE_OUTPUT_DIR)/test.exe
	$<

##################
# Negative tests #
##################

# Each file in negative/ must be rejected by 3D under --api pulse, and
# src/Test.3d must be rejected under --api lowstar.
negative_dir=$(EVERPARSE_OUTPUT_DIR)/negative

negative-test: | $(EVERPARSE_OUTPUT_DIR)
	mkdir -p $(negative_dir)
	set -e; for f in negative/*.3d; do \
	  if $(EVERPARSE_CMD) --odir $(negative_dir) --no_batch $$f > $(negative_dir)/out.log 2>&1; then \
	    echo "FAIL: 3D accepted $$f"; cat $(negative_dir)/out.log; exit 1; \
	  else echo "3D rejected $$f as expected: $$(grep -m1 Error $(negative_dir)/out.log)"; fi; \
	done
	if $(EVERPARSE_EXE) --api lowstar --odir $(negative_dir) --no_batch $(EVERPARSE_INPUT_DIR)/Test.3d > $(negative_dir)/out.log 2>&1; then \
	  echo "FAIL: 3D accepted {:error-code ...} under --api lowstar"; exit 1; \
	else echo "3D rejected --api lowstar as expected: $$(grep -m1 Error $(negative_dir)/out.log)"; fi

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

world: test negative-test

.PHONY: all world test negative-test clean
