all: FStar.do karamel.do pulse.do hacl-star

export ADMIT=1

export EVERPARSE_OPT_PATH=$(realpath .)

export FSTAR_EXE  := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
export KRML_HOME  := $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
export HACL_HOME := $(EVERPARSE_OPT_PATH)/hacl-star
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

include env.Makefile

submodules:
	git submodule init
	git submodule update

FStar:
	git clone "https://github.com/FStarLang/FStar" $@

karamel:
	git clone "https://github.com/FStarLang/karamel" $@

pulse:
	git clone "https://github.com/FStarLang/pulse" $@

everest:
	git clone "https://github.com/project-everest/everest" $@

FStar.do: FStar
	+$(MAKE) -C $< ADMIT=1

z3: FStar.do
	mkdir -p $@
	FStar/.scripts/get_fstar_z3.sh $(realpath .)/$@

karamel.do: karamel FStar.do z3
	+$(MAKE) -C $<

pulse.do: pulse FStar.do z3
	+$(MAKE) -C $< ADMIT=1

.PHONY: all submodules %.do
