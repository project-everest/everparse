all: FStar karamel pulse

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

FStar: submodules
	+$(MAKE) -C $@ ADMIT=1

z3: submodules
	mkdir -p $@
	FStar/.scripts/get_fstar_z3.sh $(realpath .)/$@

karamel: FStar z3
	+$(MAKE) -C $@

pulse: FStar z3
	+$(MAKE) -C $@ ADMIT=1

.PHONY: all FStar karamel z3 pulse submodules
