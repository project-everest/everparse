all: verify test

EVERCBOR_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..)

include $(EVERCBOR_SRC_PATH)/karamel.Makefile
include $(EVERCBOR_SRC_PATH)/steel.Makefile

SRC_DIRS += ..
ALREADY_CACHED := *,-CBOR.SteelST.Type.Def,

include $(EVERCBOR_SRC_PATH)/common.Makefile

KRML = $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -skip-compilation \
	 $(KRML_OPTS) \
	 -warn-error '@2@4@15'

extract-steel: $(ALL_KRML_FILES)
	$(KRML) -header header.txt -bundle 'CBOR.SteelST+CBOR.Spec.Constants+CBOR.SteelST.Type.Base+CBOR.SteelST.Type.Def+CBOR.SteelST.Match+CBOR.SteelST.Type+CBOR.SteelST.Array+CBOR.SteelST.String+CBOR.SteelST.SimpleValue+CBOR.SteelST.Int64+CBOR.SteelST.Tagged+CBOR.SteelST.Map.Base+CBOR.SteelST.Map+CBOR.SteelST.Parse=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBOR]' -no-prefix 'CBOR.*' $^
	! test -f out/CBOR.c

extract: extract-steel

test-steel: extract-steel
	$(CC) -Wall -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I $(STEEL_HOME)/include/steel -I out -c cbor_test.c

test: test-steel

.PHONY: clean extract-steel extract test-steel test
