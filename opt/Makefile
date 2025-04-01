all: FStar karamel pulse

export ADMIT=1

submodules:
	git submodule init
	git submodule update

FStar: submodules
	+$(MAKE) -C $@ FSTAR_TAG= package
	rm -rf fstar-install
	mkdir fstar-install
ifeq ($(OS),Windows_NT)
	$(error "Not sure what to do on Windows")
else
	tar xzf $@/fstar.tar.gz -C fstar-install
endif

karamel: FStar
	+$(MAKE) -C $@ FSTAR_EXE=$(realpath fstar-install/fstar/bin/fstar.exe)

pulse: FStar
	+$(MAKE) -C $@ FSTAR_EXE=$(realpath fstar-install/fstar/bin/fstar.exe)

.PHONY: all FStar karamel pulse submodules
