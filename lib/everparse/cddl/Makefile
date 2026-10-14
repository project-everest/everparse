all: tool.do

EVERPARSE_HOME := $(realpath ../../..)

# The CDDL tool (cddl.exe) and the tests are not part of the library, so they
# stay under src/cddl while the F* sources live here.
CDDL_SRC_PATH := $(EVERPARSE_HOME)/src/cddl

pulse.do: spec.do

tool.do: pulse.do
	+$(MAKE) -C $(CDDL_SRC_PATH)/tool

tests.do: tool.do
	+$(MAKE) -C $(CDDL_SRC_PATH)/tests

test: tests.do

.PHONY: tool.do tests.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do

clean: spec.clean pulse.clean
	+$(MAKE) -C $(CDDL_SRC_PATH)/tool clean
	+$(MAKE) -C $(CDDL_SRC_PATH)/tests clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
