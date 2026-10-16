# This Makefile only tests test case generation in batch mode.

ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile

EVERPARSE_API ?= lowstar
export EVERPARSE_API
3D=$(EVERPARSE_HOME)/bin/everparse-3d.exe --api $(EVERPARSE_API) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(KRML_EXE),--karamel "$(KRML_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")

all: Probe.3d
	mkdir -p out.z3-testgen
	$(3D) --batch --odir out.z3-testgen Probe.3d --z3_test Probe._primaryInPlace --z3_witnesses 10 --z3_branch_depth 5 --z3_flight_name titatu --z3_use_ptr

.PHONY: all

clean:
	rm -rf out.z3-testgen

.PHONY: clean
