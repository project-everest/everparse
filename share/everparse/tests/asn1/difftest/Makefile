# Hand translations of the ASN.1 schemas of schemas/ into the pure F* ASN.1
# DER specification (ASN1.DiffTest.*), shared by the Pulse tests of
# ../pulse, the golden test of ../tool, and the differential tests of the
# EverParse repository (src/ASN1/difftest), which also use the schemas and
# test vectors (vectors/) of this directory.

all: verify

EVERPARSE_HOME ?= $(realpath ../../../../..)

INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/lowparse $(EVERPARSE_HOME)/lib/everparse/asn1/spec

ALREADY_CACHED := *,-ASN1.DiffTest,

include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

.PHONY: all
