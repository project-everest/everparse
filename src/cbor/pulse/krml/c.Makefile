CBOR_SLICE_BACKEND := c

include extract.Makefile

parent_dir := $(realpath ..)
ifeq ($(OS),Windows_NT)
  parent_dir := $(shell cygpath -m $(parent_dir))
endif
NONDET_C_DIRECTORY:=$(parent_dir)/nondet/c-extracted
DET_C_DIRECTORY:=$(parent_dir)/det/c/extracted

$(NONDET_C_DIRECTORY)/CBORNondet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_EXE) $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Type=CBOR.Pulse.Raw.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base[rename=CBORNondetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Nondet.C=\*[rename=CBORNondet]' -no-prefix CBOR.Pulse.API.Nondet.C -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(NONDET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

$(DET_C_DIRECTORY)/CBORDet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_EXE) $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Type=CBOR.Pulse.Raw.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base[rename=CBORDetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.C.Copy+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -no-prefix CBOR.Pulse.API.Det.C.Copy -no-prefix CBOR.Pulse.Raw.Copy -no-prefix CBOR.Pulse.API.Det.Dummy -tmpdir $(DET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

extract: $(NONDET_C_DIRECTORY)/CBORNondet.c $(DET_C_DIRECTORY)/CBORDet.c

.PHONY: extract

include $(EVERPARSE_SRC_PATH)/cbor/custard.Makefile

# Custard's direct-to-C backend emits the whole program as a single translation
# unit, so each snapshot is just CBORDet.{c,h} / CBORNondet.{c,h}: there is no
# --custard_split for the C backend, hence no CBORxxxType.h, no internal/ header
# and no krmllib.h.  The public function names are unchanged -- the
# --custard_c_no_prefix lists mirror the -no-prefix flags above -- so the
# standalone C consumers (test/, example/, share/everparse/tests/cbor) compile
# and pass against this output with no source change.
$(DET_C_DIRECTORY)/custard/CBORDet.c: $(ALL_CHECKED_FILES)
	rm -rf $(dir $@)
	mkdir -p $(dir $@)
	$(CUSTARD_FSTAR) --custard_backend C --custard_monomorphize_types true \
		$(addprefix --custard_entry_module ,$(CUSTARD_DET_C_ENTRY)) \
		$(addprefix --custard_c_no_prefix ,$(CUSTARD_DET_C_NO_PREFIX)) \
		$(CUSTARD_DET_ROOT) -o $@

$(NONDET_C_DIRECTORY)/custard/CBORNondet.c: $(ALL_CHECKED_FILES)
	rm -rf $(dir $@)
	mkdir -p $(dir $@)
	$(CUSTARD_FSTAR) --custard_backend C --custard_monomorphize_types true \
		$(addprefix --custard_entry_module ,$(CUSTARD_NONDET_C_ENTRY)) \
		$(addprefix --custard_c_no_prefix ,$(CUSTARD_NONDET_C_NO_PREFIX)) \
		$(CUSTARD_NONDET_ROOT) -o $@

extract-custard: $(DET_C_DIRECTORY)/custard/CBORDet.c $(NONDET_C_DIRECTORY)/custard/CBORNondet.c

.PHONY: extract-custard
