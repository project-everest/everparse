# This Makefile only tests test case generation in batch mode.

ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe

3D=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)

3D_Z3_EXECUTABLE ?= z3-4.13.3

ifeq (,$(KRML_HOME))
  KRML_HOME := $(realpath $(EVERPARSE_HOME_)/../karamel)
endif
ifeq ($(OS),Windows_NT)
  KRML_HOME := $(shell cygpath -m "$(KRML_HOME)")
endif
export KRML_HOME

all: Probe.3d
	mkdir -p out.z3-testgen
	$(3D) --z3_executable $(3D_Z3_EXECUTABLE) --batch --odir out.z3-testgen Probe.3d --z3_test Probe._primaryInPlace --z3_witnesses 10 --z3_branch_depth 5 --z3_flight_name titatu --z3_use_ptr

.PHONY: all

clean:
	rm -rf out.z3-testgen

.PHONY: clean
