all: test

EVERPARSE_HOME := $(realpath ../../../..)

# The roundtrip test installs and uses the EverCDDL OCaml library, so it stays
# next to the tool, under src/cddl/tests.
ROUNDTRIP_PATH := $(EVERPARSE_HOME)/src/cddl/tests/roundtrip

demo.do:

dpe.do:

unit.do:

rust.do:

roundtrip.do:
	+$(MAKE) -C $(ROUNDTRIP_PATH)

.PHONY: roundtrip.do

test: demo.do dpe.do rust.do unit.do roundtrip.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do

clean: demo.clean dpe.clean rust.clean unit.clean
	+$(MAKE) -C $(ROUNDTRIP_PATH) clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
