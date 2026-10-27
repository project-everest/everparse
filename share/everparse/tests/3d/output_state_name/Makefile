# Regression test for the hygiene of the generated Pulse output state: a 3D
# mutable output parameter named `output_state` must not collide with the
# definition the Pulse backend emits, nor with the reserved state-dictionary
# key that stands for the output state.
#
# This is compile-only: `--batch` runs generation, F* verification and Custard C
# extraction, which is all that is needed -- the bug made the generated F*
# fail to typecheck. No executable is built and nothing is run.

EVERPARSE_HOME ?= $(realpath ../../../../..)
export EVERPARSE_HOME

include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/everparse-3d.exe $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)") --api pulse

EVERPARSE_OUTPUT_DIR=obj

all: world

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

world: Test.3d | $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --batch --odir $(EVERPARSE_OUTPUT_DIR) Test.3d

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all world clean
