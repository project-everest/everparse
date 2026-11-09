# Tests of the ASN.1 DER library (lib/everparse/asn1) and of
# everparse-asn1, against an EverParse repository or binary package
# (EVERPARSE_HOME).
#
#   difftest: the hand-written F* schemas of the differential tests
#   pulse:    their Pulse validators, extracted to C and run on the
#             test vectors, and other C tests of the Pulse library
#   tool:     everparse-asn1 on test schemas, compiled and run

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

all: difftest pulse tool

difftest pulse tool:
	+$(MAKE) -C $@

pulse tool: difftest

clean:
	+$(MAKE) -C difftest clean
	+$(MAKE) -C pulse clean
	+$(MAKE) -C tool clean

.PHONY: all difftest pulse tool clean
