# The EverParse/3d inplace hash checker, extracted to F#.
#
# Custard's F# backend (doc/ref/custard.md section 122) emits one whole
# program per run: the module, the FStarCustard.fs support library it is
# written against, and a project file. There is no --custard_split, so this
# is two runs rather than one extraction per module, one for each of the two
# .NET programs under hashchk/.
#
# The interface-only modules OS and Hashing.Op are realized by the
# hand-written hashchk/OS.fs and hashchk/Hashing_Op.fs. Their .fsti files
# carry [@@custard_extern "..."] naming exactly those F# symbols -- the same
# names the OCaml build of 3d uses, which is why one attribute serves both
# backends.

EVERPARSE_HOME=$(realpath ../..)

FSTAR_EXE ?= fstar.exe

OTHERFLAGS?=

OUTPUT_DIR=hashchk/3d

FSTAR=$(FSTAR_EXE) $(OTHERFLAGS) --include $(EVERPARSE_HOME)/src/3d/prelude --already_cached '*,' --codegen Custard --custard_backend FSharp

# What hashchk/HashCheck.fs calls into. Dead code elimination is by
# reachability from these, so anything omitted here is simply not emitted.
HASHCHK_ENTRIES = \
  Hashing.Hash.c_comment_intro \
  Hashing.Hash.check_inplace_hashes \
  Hashing.Hash.check_all_hashes \
  Options.Base.parse_cmd_line \
  Options.Base.check_inplace_hashes \
  Options.Base.output_dir \
  Options.Base.check_hashes \
  Options.Base.module_name \

all: extract-hashchk

.PHONY: all extract-hashchk

extract-hashchk:
	rm -rf $(OUTPUT_DIR)
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) $(addprefix --custard_entry ,$(HASHCHK_ENTRIES)) Hashing.Hash.fst -o $(OUTPUT_DIR)/HashChk.fs
	$(FSTAR) --custard_entry Version.everparse_version Version.fst -o $(OUTPUT_DIR)/EverParseVersion.fs
	rm -f $(OUTPUT_DIR)/HashChk.fsproj $(OUTPUT_DIR)/EverParseVersion.fsproj
