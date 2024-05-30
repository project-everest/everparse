all: verify test

EVERCBOR_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../everparse) $(EVERCBOR_SRC_PATH)/lowparse $(EVERCBOR_SRC_PATH)/lowparse/steel

include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/steel.Makefile

INCLUDE_PATHS += $(STEEL_LIB)/c

ALREADY_CACHED := *,-CBOR,

ifneq (,$(STEEL_C))
  INCLUDE_PATHS += $(EVERCBOR_SRC_PATH)/lowparse/steel/steel_c_array
else
  FSTAR_OPTIONS += --include $(EVERCBOR_SRC_PATH)/lowparse/steel/steel_array
endif

include $(EVERCBOR_SRC_PATH)/common.Makefile

KRML = $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -skip-linking \
	 $(KRML_OPTS) \
	 -warn-error '@2@4@15'

CBOR.SteelC.fst.checked: FSTAR_OPTIONS += --ext compat:open_metas

extract-steelc: $(filter-out CBOR_SteelST%,$(ALL_KRML_FILES)) $(filter CBOR_SteelST_Raw%,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelC+CBOR.SteelST.Raw+CBOR.Spec.Constants=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBORSteelC]' $^

extract-steel-raw: $(filter-out CBOR_SteelC% CBOR_SteelST%,$(ALL_KRML_FILES)) $(filter CBOR_SteelST_Raw%,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelST.Raw+CBOR.Spec.Constants=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBORRaw]' $^

extract-steel: $(filter-out CBOR_SteelC%,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelST+CBOR.Spec.Constants+CBOR.SteelST.Type.Base+CBOR.SteelST.Type.Def+CBOR.SteelST.Match+CBOR.SteelST.Type+CBOR.SteelST.Array+CBOR.SteelST.String+CBOR.SteelST.SimpleValue+CBOR.SteelST.Int64+CBOR.SteelST.Tagged+CBOR.SteelST.Map.Base+CBOR.SteelST.Map+CBOR.SteelST.Parse=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBOR]' -no-prefix 'CBOR.*' $^

extract: extract-steelc extract-steel extract-steel-raw

test-steel-raw: extract-steel-raw
	$(CC) -Wall -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I $(STEEL_HOME)/include/steel -I out -c cbor_unverified.c

test-steel: extract-steel

test-steelc: extract-steelc

test: test-steel test-steelc test-steel-raw

.PHONY: clean extract-steel extract-steelc extract test-steel test-steelc test extract-steel-raw test-steel-raw
