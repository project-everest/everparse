# Specification tests: client theorems about the actions of generated
# validators, stated against the functional specification of actions
# (EverParse3d.Actions.Spec, EverParse3d.Actions.ValueSpec) and proven in F*.
#
# For each src/X.3d, 3d generates, verifies and extracts X, then the
# hand-written src/X.Lemmas.fsti and src/X.Lemmas.fst (a `friend` of X) are
# verified against it. Each Lemmas file also checks, with `expect_failure`,
# that wrong claims are rejected, so the specs are not vacuous.
#
# SpecPeep.3d uses field_ptr_after, which needs a static (or extern) input
# stream, so it goes to its own output directory.

all: world

EVERPARSE_HOME ?= $(realpath ../../../../..)
export EVERPARSE_HOME

include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
3D=$(EVERPARSE_HOME)/bin/everparse-3d.exe $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)") --api pulse

obj/SpecTest.Lemmas.fst.checked: src/SpecTest.3d src/SpecTest.Lemmas.fsti src/SpecTest.Lemmas.fst
	rm -rf obj
	mkdir -p obj
	$(3D) --odir obj --batch src/SpecTest.3d
	cp src/SpecTest.Lemmas.fsti src/SpecTest.Lemmas.fst obj/
	$(3D) --odir obj --__micro_step verify obj/SpecTest.Lemmas.fsti
	$(3D) --odir obj --__micro_step verify obj/SpecTest.Lemmas.fst

obj-peep/SpecPeep.Lemmas.fst.checked: src/SpecPeep.3d src/SpecPeep.Lemmas.fsti src/SpecPeep.Lemmas.fst
	rm -rf obj-peep
	mkdir -p obj-peep
	$(3D) --input_stream static --input_stream_include EverParseStream.h --odir obj-peep --batch src/SpecPeep.3d
	cp src/SpecPeep.Lemmas.fsti src/SpecPeep.Lemmas.fst obj-peep/
	$(3D) --odir obj-peep --__micro_step verify obj-peep/SpecPeep.Lemmas.fsti
	$(3D) --odir obj-peep --__micro_step verify obj-peep/SpecPeep.Lemmas.fst

world: obj/SpecTest.Lemmas.fst.checked obj-peep/SpecPeep.Lemmas.fst.checked

clean:
	rm -rf obj obj-peep

.PHONY: all world clean
