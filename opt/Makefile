all: FStar.do karamel.do pulse.do z3 python-venv.do qcbor.do tinycbor.do hacl-star.do dice.do lowparse.do

.PHONY: all %.do

opam-env.Makefile: everest
	opam init --no-setup --root=opam --kind=local --compiler=5.3.0 default ./opam-repository
	opam exec --root=opam --set-root -- everest/everest opam
	./opam-env.sh > $@

export EVERPARSE_OPT_PATH=$(realpath .)
export EVERPARSE_SRC_PATH=$(realpath ../src)

include opam-env.Makefile

export ADMIT=1
export OTHERFLAGS=--admit_smt_queries true # because Karamel Makefiles do not honor ADMIT

export FSTAR_EXE  := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
export KRML_HOME  := $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
export PATH := $(realpath $(EVERPARSE_OPT_PATH)/..)/bin:$(EVERPARSE_OPT_PATH)/z3:$(PATH)

include env.Makefile

include git-clone.Makefile

FStar.do: FStar
	+$(MAKE) -C $< ADMIT=1

z3: FStar
	mkdir -p $@
	FStar/.scripts/get_fstar_z3.sh $(realpath .)/$@
	rm -rf $@/z3-4.8.5

karamel.do: karamel FStar.do
	+$(MAKE) -C $<

pulse.do: pulse FStar.do
	+$(MAKE) -C $< ADMIT=1

python-venv.do: $(EVERPARSE_SRC_PATH)/cose/.venv

$(EVERPARSE_SRC_PATH)/cose/.venv:
	+$(MAKE) -C $(dir $@) $(notdir $@)

qcbor.do: $(EVERPARSE_SRC_PATH)/cddl/tests/unit/QCBOR
	+$(MAKE) -C $(dir $<) -f qcbor.Makefile

$(EVERPARSE_SRC_PATH)/cddl/tests/unit/QCBOR:
	+$(MAKE) -C $(dir $@) $(notdir $@)

tinycbor.do: $(EVERPARSE_SRC_PATH)/cddl/tests/unit/tinycbor
	+$(MAKE) -C $(dir $<) -f tinycbor.Makefile

$(EVERPARSE_SRC_PATH)/cddl/tests/unit/tinycbor:
	+$(MAKE) -C $(dir $@) $(notdir $@)

hacl-star.do: $(EVERPARSE_SRC_PATH)/cose/verifiedinterop/test/hacl-star karamel
	+$(MAKE) -C $</dist/gcc-compatible

$(EVERPARSE_SRC_PATH)/cose/verifiedinterop/test/hacl-star:
	+$(MAKE) -C $(dir $@) $(notdir $@)

dice.do: pulse.do
	+$(MAKE) -C $(EVERPARSE_SRC_PATH)/cddl/tests/dpe -f dice.Makefile

# This is LowParse from Ramananandro et al.'s EverParse (USENIX Security 2019)
lowparse.do: karamel.do
	+$(MAKE) -C $(EVERPARSE_SRC_PATH)/lowparse
