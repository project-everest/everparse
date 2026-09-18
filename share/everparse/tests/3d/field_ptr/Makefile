# Test that field_ptr, field_pos_64 and field_pos_32 report the offset at which
# the annotated field starts, rather than the offset just past it.
#
# This uses the default (buffer) input stream, which is the only backend that
# supports field_ptr.

all: world

########################################################
# Variables needed by the EverParse-generated Makefile #
########################################################

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --pulse

EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src

#########################################
# Generating and including the Makefile #
#########################################

everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

$(everparse_makefile): $(wildcard src/*.3d) $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ src/Test.3d

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

#############################
# Building the test program #
#############################

all_o_files=$(EVERPARSE_ALL_O_FILES) $(EVERPARSE_OUTPUT_DIR)/main.o

# Under --pulse, EverParse.h is not copied from the prelude at the start of
# the pipeline: KaRaMeL emits it, carrying the bundled runtime, at the same
# time as the generated .c files. The wrapper headers include it, so it has
# to be an explicit prerequisite here, or a parallel build races.
$(EVERPARSE_OUTPUT_DIR)/main.o: $(EVERPARSE_INPUT_DIR)/main.c $(EVERPARSE_OUTPUT_DIR)/TestWrapper.h $(EVERPARSE_OUTPUT_DIR)/EverParse.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_OUTPUT_DIR) -c -o $@ $<

$(EVERPARSE_OUTPUT_DIR)/test.exe: $(all_o_files)
	$(CC) $(LDFLAGS) -o $@ $^

test: $(EVERPARSE_OUTPUT_DIR)/test.exe
	$<

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

world: test

.PHONY: all world test clean
