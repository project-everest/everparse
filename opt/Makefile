all: FStar karamel pulse

export ADMIT=1

export EVERPARSE_OPT_PATH=$(realpath .)

include env.Makefile

submodules:
	git submodule init
	git submodule update

FStar: submodules
	+$(MAKE) -C $@ 1

z3: submodules
	mkdir -p $@
	FStar/.scripts/get_fstar_z3.sh $(realpath .)/$@

karamel: FStar z3
	+$(MAKE) -C $@

pulse: FStar z3
	+$(MAKE) -C $@

.PHONY: all FStar karamel z3 pulse submodules
