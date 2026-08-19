all: FStar.do karamel.do pulse.do z3

export ADMIT=1
export OTHERFLAGS=--admit_smt_queries true # because Karamel Makefiles do not honor ADMIT

export EVERPARSE_OPT_PATH=$(realpath .)

export FSTAR_EXE  := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
export KRML_HOME  := $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

include env.Makefile

submodules:
	git submodule init
	git submodule update

FStar:
	git clone "https://github.com/FStarLang/FStar" $@
	cd $@ && git checkout 627e8590a81fd0afb9d9b20391105d7d355922b4

karamel:
	git clone "https://github.com/FStarLang/karamel" $@
	cd $@ && git checkout 354791911c6b40d15a41cda7a0e3560da1cf31a1

pulse:
	git clone "https://github.com/FStarLang/pulse" $@
	cd $@ && git checkout 5080e77ae60d2e7e30e2f6a1c3d2ec1f61d1a9df

everest:
	git clone "https://github.com/project-everest/everest" $@

FStar.do: FStar
	+$(MAKE) -C $< ADMIT=1

z3: FStar.do
	mkdir -p $@
	FStar/.scripts/get_fstar_z3.sh $(realpath .)/$@
	rm -rf $@/z3-4.8.5

karamel.do: karamel FStar.do
	+$(MAKE) -C $<

pulse.do: pulse FStar.do
	+$(MAKE) -C $< ADMIT=1

.PHONY: all submodules %.do
