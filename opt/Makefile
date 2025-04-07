all: FStar karamel pulse

export ADMIT=1

submodules:
	git submodule init
	git submodule update

FStar: submodules
	+$(MAKE) -C $@ 1

karamel: FStar
	+$(MAKE) -C $@ FSTAR_EXE=$(realpath FStar/bin/fstar.exe)

pulse: FStar
	+$(MAKE) -C $@ FSTAR_EXE=$(realpath FStar/bin/fstar.exe)

.PHONY: all FStar karamel pulse submodules
