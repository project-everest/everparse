# Test for --wrapper_error_code out|return (--api pulse only).
#
# WrapperErrorCode.3d is extracted with --batch once per variant, each into
# its own output directory, and every variant is linked against main.c,
# which checks the error codes conveyed by the wrappers. The `*styled'
# variants check that the option composes with the C style options.
# Finally, 3D must reject the option under --api lowstar, and the `return'
# mode with a non-buffer input stream.

SRC_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))
EVERPARSE_HOME ?= $(realpath $(SRC_DIR)/../../../../..)
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_EXE = $(EVERPARSE_HOME)/bin/everparse-3d.exe $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")
OUTPUT_DIR = output

CC ?= cc

variants := default styled return return_styled

style_options := --hoist_locals --init_locals c89 --goto_for_early_return

options_common := --api pulse --complete_wrappers
options_default := --wrapper_error_code out
options_styled := --wrapper_error_code out $(style_options)
options_return := --wrapper_error_code return
options_return_styled := --wrapper_error_code return $(style_options)

cflags_return := -DWRAPPER_ERROR_CODE_RETURN
cflags_return_styled := -DWRAPPER_ERROR_CODE_RETURN

TEST_CFLAGS = -Wall -Wextra -Werror -pedantic -std=c11

all: test

.PHONY: all test clean negative-test

.PRECIOUS: $(OUTPUT_DIR)/%/.extracted
$(OUTPUT_DIR)/%/.extracted: $(SRC_DIR)/WrapperErrorCode.3d
	rm -rf $(OUTPUT_DIR)/$*
	mkdir -p $(OUTPUT_DIR)/$*
	$(EVERPARSE_EXE) --batch --odir $(OUTPUT_DIR)/$* $(options_common) $(options_$*) $<
	touch $@

.PRECIOUS: $(OUTPUT_DIR)/%/test.exe
$(OUTPUT_DIR)/%/test.exe: $(OUTPUT_DIR)/%/.extracted $(SRC_DIR)/main.c
	$(CC) $(TEST_CFLAGS) $(cflags_$*) -I $(OUTPUT_DIR)/$* -o $@ \
	  $(SRC_DIR)/main.c $(OUTPUT_DIR)/$*/WrapperErrorCode.c $(OUTPUT_DIR)/$*/WrapperErrorCodeWrapper.c

run_targets := $(addprefix run-,$(variants))
.PHONY: $(run_targets)
$(run_targets): run-%: $(OUTPUT_DIR)/%/test.exe
	$<

negative-test:
	mkdir -p $(OUTPUT_DIR)/negative
	if $(EVERPARSE_EXE) --api lowstar --wrapper_error_code out --odir $(OUTPUT_DIR)/negative $(SRC_DIR)/WrapperErrorCode.3d > $(OUTPUT_DIR)/negative/out.log 2>&1; then \
	  echo "FAIL: 3D accepted --wrapper_error_code under --api lowstar"; exit 1; \
	else grep -F -- '--wrapper_error_code: only supported with --api pulse' $(OUTPUT_DIR)/negative/out.log; fi
	if $(EVERPARSE_EXE) --api pulse --input_stream extern --wrapper_error_code return --odir $(OUTPUT_DIR)/negative $(SRC_DIR)/WrapperErrorCode.3d > $(OUTPUT_DIR)/negative/out-return.log 2>&1; then \
	  echo "FAIL: 3D accepted --wrapper_error_code return under --input_stream extern"; exit 1; \
	else grep -F -- '--wrapper_error_code return: only supported with --input_stream buffer' $(OUTPUT_DIR)/negative/out-return.log; fi
	if $(EVERPARSE_EXE) --api pulse --wrapper_error_code bogus --odir $(OUTPUT_DIR)/negative $(SRC_DIR)/WrapperErrorCode.3d > $(OUTPUT_DIR)/negative/out-bogus.log 2>&1; then \
	  echo "FAIL: 3D accepted --wrapper_error_code bogus"; exit 1; \
	else grep -F -- 'wrong argument given to option `wrapper_error_code`' $(OUTPUT_DIR)/negative/out-bogus.log; fi

test: $(run_targets) negative-test

clean:
	rm -rf $(OUTPUT_DIR)
