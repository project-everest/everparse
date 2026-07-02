CBOR_SLICE_BACKEND := c

include extract.Makefile

NONDET_C_DIRECTORY:=$(realpath ..)/nondet/c-extracted
DET_C_DIRECTORY:=$(realpath ../det/c)/extracted

$(NONDET_C_DIRECTORY)/CBORNondet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Type=CBOR.Pulse.Raw.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base[rename=CBORNondetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Nondet.C=\*[rename=CBORNondet]' -no-prefix CBOR.Pulse.API.Nondet.C -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(NONDET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

$(DET_C_DIRECTORY)/CBORDet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Type=CBOR.Pulse.Raw.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base[rename=CBORDetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.C.Copy+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -no-prefix CBOR.Pulse.API.Det.C.Copy -no-prefix CBOR.Pulse.Raw.Copy -no-prefix CBOR.Pulse.API.Det.Dummy -tmpdir $(DET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

extract: $(NONDET_C_DIRECTORY)/CBORNondet.c $(DET_C_DIRECTORY)/CBORDet.c

.PHONY: extract
