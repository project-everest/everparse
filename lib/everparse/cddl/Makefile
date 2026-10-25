all: tool.do

EVERPARSE_HOME := $(realpath ../../..)

# The CDDL tool (everparse-cddl.exe) is not part of the library, so it stays under
# src/cddl while the F* sources live here, and the tests live under
# share/everparse/tests/cddl.
CDDL_SRC_PATH := $(EVERPARSE_HOME)/src/cddl
CDDL_TESTS_PATH := $(EVERPARSE_HOME)/share/everparse/tests/cddl

pulse.do: spec.do

tool.do: pulse.do
	+$(MAKE) -C $(CDDL_SRC_PATH)/tool

tests.do: tool.do
	+$(MAKE) -C $(CDDL_TESTS_PATH)

test: tests.do

.PHONY: tool.do tests.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do

clean: spec.clean pulse.clean
	+$(MAKE) -C $(CDDL_SRC_PATH)/tool clean
	+$(MAKE) -C $(CDDL_TESTS_PATH) clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
