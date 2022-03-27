EVERPARSE_HOME ?= ../..
QD_BUILD = _build/default/quackyducky.exe
QD_BIN = $(EVERPARSE_HOME)/bin/qd.exe

all: $(QD_BIN)

$(QD_BIN): $(QD_BUILD)
	mkdir -p $(dir $@)
	cp $< $@
	chmod +w $@ # because dune produces read-only executables

$(QD_BUILD): $(filter-out %~,$(wildcard *.ml*))
	dune build

clean:
	dune clean
	rm -rf $(QD_BIN)

.PHONY: all clean
