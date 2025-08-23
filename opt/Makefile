all: FStar.do karamel.do pulse.do z3

.PHONY: all %.do

opam-env.Makefile: everest
	opam init --no-setup --root=opam
	opam exec --root=opam --set-root -- env OPAMNODEPEXTS=1 everest/everest opam
	./opam-env.sh > $@

export EVERPARSE_OPT_PATH=$(realpath .)

include opam-env.Makefile

export ADMIT=1
export OTHERFLAGS=--admit_smt_queries true # because Karamel Makefiles do not honor ADMIT

export FSTAR_EXE  := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
export KRML_HOME  := $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

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
