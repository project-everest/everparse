all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../..)

CDDLTest.Test.fst: cose.cddl ../spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ > $@.tmp
	mv $@.tmp $@

extract-all: CDDLTest.Test.fst
	+$(MAKE) -f extract.Makefile extract

.PHONY: extract-all all

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
