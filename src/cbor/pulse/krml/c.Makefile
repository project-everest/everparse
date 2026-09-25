CBOR_SLICE_BACKEND := c
CBOR_API ?= det

# The roots of this pass: every module named on the left of a karamel -bundle
# clause below, plus the bundle names themselves (see extract.Makefile).
ifeq (det,$(CBOR_API))
CUSTARD_ENTRY_MODULES := CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.C
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.C.Copy
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := $(realpath ../raw/CBOR.Pulse.API.Det.C.Copy.fst)
else
CUSTARD_ENTRY_MODULES := CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Nondet.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Nondet.C
CUSTARD_ROOTS := $(realpath ../raw/CBOR.Pulse.API.Nondet.C.fst)
endif

include extract.Makefile

parent_dir := $(realpath ..)
ifeq ($(OS),Windows_NT)
  parent_dir := $(shell cygpath -m $(parent_dir))
endif
NONDET_C_DIRECTORY:=$(parent_dir)/nondet/c-extracted
DET_C_DIRECTORY:=$(parent_dir)/det/c/extracted

ifeq (det,$(CBOR_API))

$(DET_C_DIRECTORY)/CBORDet.c: $(CUSTARD_KRML)
	mkdir -p $(dir $@)
	$(KRML_EXE) $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Type=CBOR.Pulse.Raw.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base,Prims,Custard.\*[rename=CBORDetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.C.Copy+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -no-prefix CBOR.Pulse.API.Det.C.Copy -no-prefix CBOR.Pulse.Raw.Copy -no-prefix CBOR.Pulse.API.Det.Dummy -tmpdir $(DET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

extract: $(DET_C_DIRECTORY)/CBORDet.c

else

$(NONDET_C_DIRECTORY)/CBORNondet.c: $(CUSTARD_KRML)
	mkdir -p $(dir $@)
	$(KRML_EXE) $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Type=CBOR.Pulse.Raw.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base,Prims,Custard.\*[rename=CBORNondetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Nondet.C=\*[rename=CBORNondet]' -no-prefix CBOR.Pulse.API.Nondet.C -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(NONDET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

extract: $(NONDET_C_DIRECTORY)/CBORNondet.c

endif

.PHONY: extract
