all: 3d prelude

EVERPARSE_SRC_PATH=$(realpath ..)
EVERPARSE_HOME=$(realpath ../..)

FSTAR_FILES := Main.fst Version.fst
FSTAR_DEP_OPTIONS := --extract '* -Prims -FStar'
OUTPUT_DIRECTORY := ocaml/generated

include $(EVERPARSE_SRC_PATH)/common.Makefile

EVERPARSE_3D=$(EVERPARSE_HOME)/bin/3d.exe
EVERPARSE_3D_MAIN=ocaml/_build/default/Main.exe

test: demo

demo: all
	+$(MAKE) -C tests

.PHONY: all prelude test clean clean-3d clean-prelude 3d

prelude:
	+$(MAKE) -C prelude

Version.fst:
	env EVERPARSE_HOME=$(EVERPARSE_HOME) ./version.sh

3d: $(EVERPARSE_3D)

$(EVERPARSE_3D): $(EVERPARSE_3D_MAIN)
	mkdir -p $(dir $@)
	cp $< $@
	chmod +w $@ # because dune produces read-only executables

$(EVERPARSE_3D_MAIN): $(ALL_ML_FILES) $(filter-out %~,$(wildcard ocaml/*.ml*))
	+$(MAKE) -C ocaml

clean-prelude:
	+$(MAKE) -C prelude clean

clean-3d:
	+$(MAKE) -C ocaml clean
	rm -rf *.checked *~ Version.fst $(EVERPARSE_HOME)/bin/3d.exe

clean: clean-3d clean-prelude
