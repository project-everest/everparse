EVERPARSE_HOME ?= $(realpath ../../../../..)
EVERPARSE_SRC_PATH ?= $(EVERPARSE_HOME)/src
QD_EXE ?= $(EVERPARSE_HOME)/bin/qd.exe

all: extracted/Makefile Test.fst
	+$(MAKE) -C extracted

extracted/Makefile: $(QD_EXE) unittests.rfc bitcoin.rfc extracted.Makefile
	mkdir -p extracted
	rm -f extracted/*.fst extracted/*.fsti
	$(QD_EXE) -odir extracted -pulse unittests.rfc
#	$(QD_EXE) -low -odir extracted bitcoin.rfc
	rm -f $@
	cp extracted.Makefile $@
	touch $@

clean:
	rm -rf extracted

.PHONY: all clean
