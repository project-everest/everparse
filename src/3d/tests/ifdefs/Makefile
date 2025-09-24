# This Makefile is meant to be used with GNU Make. It builds EverParse
# validators and parsers corresponding to the data formats specified
# in src/*.3d files, as well as a test program to run them.

# Default rule when `make` is run without argument. This rule MUST
# appear first, so we define it here and make it point to a `world`
# rule that will depend on variables defined in the
# EverParse-generated Makefile.
all: world

########################################################
# Variables needed by the EverParse-generated Makefile #
########################################################

# EVERPARSE_HOME: root of the EverParse tree (source tree or contents
# of the binary package.)
# EVERPARSE_HOME is necessary for the 3d executable. It needs to point to the
# root of the EverParse source tree. However, EVERPARSE_HOME is not needed if
# you run everparse.sh or everparse.cmd from the binary package.
EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

# Command to run EverParse: path to either the 3d executable or the
# everparse.sh or everparse.cmd script from the EverParse binary
# package; followed by arguments
FSTAR_EXE ?= fstar.exe
EVERPARSE_EXE=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)
EVERPARSE_CMD=$(EVERPARSE_EXE) --config $(EVERPARSE_INPUT_DIR)/CompileTimeIfFlags.3d.config

# Output directory for .c/.h files as well as temporary files (.fst,
# .krml, etc.)
EVERPARSE_OUTPUT_DIR=obj

# Input directory containing .3d (and auxiliary .3d.copyright.txt)
# files
EVERPARSE_INPUT_DIR=src

#########################################
# Generating and including the Makefile #
#########################################

# Define the name and path of the generated Makefile. We cleverly
# decide to have it generated into the output directory along with all
# temporary files.
everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

# Create the output directory if it does not exist
$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

# Generate the Makefile if any .3d file is modified
$(everparse_makefile): $(wildcard src/*.3d) $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ $(wildcard $(EVERPARSE_INPUT_DIR)/*.3d)

# Include the generated Makefile
ifeq (,$(filter clean,$(MAKECMDGOALS)))
include $(everparse_makefile)
endif

#######################################################
# Specifying the `world` rule run by the default rule #
#######################################################

# Specify the behavior of the default rule
world: $(EVERPARSE_OUTPUT_DIR)/CompileTimeIf.o $(EVERPARSE_OUTPUT_DIR)/AnonNestedStructIfDefs.o $(EVERPARSE_ALL_C_FILES) batch

#######################################################
# Also test batch mode
#######################################################

EVERPARSE_BATCH_OUTPUT_DIR=batch_obj

$(EVERPARSE_BATCH_OUTPUT_DIR):
	mkdir -p $@

batch: $(EVERPARSE_BATCH_OUTPUT_DIR)
	$(EVERPARSE_CMD) --batch --odir $(EVERPARSE_BATCH_OUTPUT_DIR) $(wildcard $(EVERPARSE_INPUT_DIR)/*.3d)

# Declare all phony rules.
# Cf. https://www.gnu.org/software/make/manual/html_node/Phony-Targets.html
.PHONY: all world test clean batch

###########
# Cleanup #
###########

# Since everything is output to the same directory, including the
# generated Makefile, it is enough to remove that directory.
clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR) $(EVERPARSE_BATCH_OUTPUT_DIR)
