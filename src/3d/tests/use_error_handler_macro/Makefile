# Test for the --use_error_handler_macro 3D option.
#
# 3D is invoked with --use_error_handler_macro so the generated
# validators rely on the EVERPARSE_ERROR_HANDLER_MACRO C macro instead
# of a dynamic error-handler callback.  The macro is provided by
# src/MyErrorHandlerMacro.h, which is injected into every generated
# .c/.h file via --add_include.

all: world

########################################################
# Variables needed by the EverParse-generated Makefile #
########################################################

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
EVERPARSE_EXE=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)

# The option under test plus an --add_include so the user-provided
# macro definition is visible from all generated .c/.h files.
EVERPARSE_OPTIONS=--use_error_handler_macro --add_include '"MyErrorHandlerMacro.h"'

EVERPARSE_CMD=$(EVERPARSE_EXE) $(EVERPARSE_OPTIONS)

EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src

#########################################
# Generating and including the Makefile #
#########################################

everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

$(everparse_makefile): $(wildcard src/*.3d) $(EVERPARSE_INPUT_DIR)/MyErrorHandlerMacro.h $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ src/Test.3d
	cp $(EVERPARSE_INPUT_DIR)/MyErrorHandlerMacro.h $(EVERPARSE_OUTPUT_DIR)/

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

#############################
# Building the test program #
#############################

all_o_files=$(EVERPARSE_ALL_O_FILES) $(EVERPARSE_OUTPUT_DIR)/main.o

$(EVERPARSE_OUTPUT_DIR)/main.o: $(EVERPARSE_INPUT_DIR)/main.c $(EVERPARSE_OUTPUT_DIR)/TestWrapper.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_OUTPUT_DIR) -c -o $@ $<

$(EVERPARSE_OUTPUT_DIR)/test.exe: $(all_o_files)
	$(CC) $(LDFLAGS) -o $@ $^

test: $(EVERPARSE_OUTPUT_DIR)/test.exe
	$<

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

world: test

.PHONY: all world test clean
