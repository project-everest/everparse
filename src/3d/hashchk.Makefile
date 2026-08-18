ROOT=Hashing.Hash.fst Options.fst

EVERPARSE_HOME=$(realpath ../..)

FSTAR_EXE ?= fstar.exe

INCLUDE_PATHS=
OTHERFLAGS?=
FSTAR=$(FSTAR_EXE) $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS) $(EVERPARSE_HOME)/src/3d/prelude) --already_cached '*,'

all: extract-hashchk

.PHONY: all extract-hashchk

OUTPUT_DIR=hashchk/3d

%.fs:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen FSharp --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir $(OUTPUT_DIR)

hashchk.depend: $(wildcard *.fst *.fsti) Version.fst
	$(FSTAR) --odir $(OUTPUT_DIR) --dep full $(ROOT) --extract '* -Prims -FStar' --output_deps_to $@

include hashchk.depend

extract-hashchk: $(ALL_FS_FILES)

# For fstarlib only

FSTAR_HOME := $(EVERPARSE_HOME)/opt/FStar

.PHONY: fstarlib

FSTARLIB_FILES= \
  extracted/FStar_Pervasives.fs \
  FStar_List_Tot_Base.fs \
  FStar_Char.fs \
  FStar_Monotonic_Heap.fs \
  FStar_CommonST.fs \
  FStar_IO.fs \


fstarlib:
	rm -rf hashchk/fstarlib
	mkdir -p hashchk/fstarlib
	cp $(addprefix $(FSTAR_HOME)/fsharp/base/,$(FSTARLIB_FILES)) hashchk/fstarlib/
