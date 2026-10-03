all: 3d prelude

EVERPARSE_SRC_PATH=$(realpath ..)
EVERPARSE_HOME=$(realpath ../..)

FSTAR_FILES := Main.fst Version.fst
FSTAR_FILES += Hashing.Hash.fst
OUTPUT_DIRECTORY := ocaml/generated

# The 3d compiler is a whole program: Main's top-level initializer is what it
# runs, and the hand-written OCaml under ocaml/ (which realizes the
# interface-only modules Batch, JSON, OS, Z3, ...) calls into the generated
# code, so every definition it calls has to be a root too -- dead code
# elimination cannot see a call from hand-written OCaml.
CUSTARD_BACKEND := OCaml
# The parser (ocaml/parser.mly, ocaml/lexer.mll) builds every shape of the
# source AST, so all of Ast is public surface.
CUSTARD_ENTRY_MODULES := Ast
CUSTARD_ENTRIES := Main
CUSTARD_ENTRIES += Deps.get_config
CUSTARD_ENTRIES += HashingOptions.input_stream_include
CUSTARD_ENTRIES += Options.config_module_name
CUSTARD_ENTRIES += Options.get_blank_lines
CUSTARD_ENTRIES += Options.get_goto_for_early_return
CUSTARD_ENTRIES += Options.get_hoist_locals
CUSTARD_ENTRIES += Options.get_init_locals
CUSTARD_ENTRIES += Options.get_line_comments
CUSTARD_ENTRIES += Options.z3_executable
CUSTARD_ENTRIES += Options.z3_options
CUSTARD_ENTRIES += Version.everparse_version
CUSTARD_ENTRIES += Config.config
CUSTARD_ENTRIES += Config.config_compile_time_flags
CUSTARD_ENTRIES += Hashing.Hash.check_all_hashes
CUSTARD_ENTRIES += Hashing.Hash.check_inplace_hashes
CUSTARD_ENTRIES += Hashing.Hash.hash_as_comment
CUSTARD_ENTRIES += Hashing.Hash.hashed_files
# The interface-only modules that ocaml/ realizes by hand. Only those that
# declare an abstract type need to be named: a module whose declarations are
# all values gets no generated file to begin with.
CUSTARD_REALIZED_MODULES := Hashing_Op Hashtable Z3

# One file on the command line: the rest of the program is loaded on demand
# from the names above.
CUSTARD_ROOTS := Main.fst

clean_rules += clean-prelude clean-3d

include $(EVERPARSE_SRC_PATH)/common.Makefile

EVERPARSE_3D=$(EVERPARSE_HOME)/bin/3d.exe
EVERPARSE_3D_MAIN=ocaml/_build/default/Main.exe

test: demo

demo: all
	+$(MAKE) -C tests

.PHONY: all prelude test clean clean-3d clean-prelude 3d

prelude:
	+$(MAKE) -C prelude

Version.fst:
	env EVERPARSE_HOME=$(EVERPARSE_HOME) ./version.sh > $@.tmp
	mv $@.tmp $@

3d: $(EVERPARSE_3D)

$(EVERPARSE_3D): $(EVERPARSE_3D_MAIN)
	mkdir -p $(dir $@)
	cp $< $@
	chmod +w $@ # because dune produces read-only executables

$(EVERPARSE_3D_MAIN): $(CUSTARD_STAMP) $(filter-out %~,$(wildcard ocaml/*.ml*))
	+$(MAKE) -C ocaml

clean-prelude:
	+$(MAKE) -C prelude clean

.PHONY: clean-prelude

clean-3d:
	+$(MAKE) -C ocaml clean
	rm -rf *.checked *~ Version.fst $(EVERPARSE_HOME)/bin/3d.exe

.PHONY: clean-3d

.PHONY: hashchk hashchk-boot hashchk-rebuild

hashchk:
	cd hashchk && dotnet build everparse.fsproj && dotnet build everparse-hashchk.fsproj

# Re-extract the hash checker from F* and rebuild it. Contrary to
# hashchk-boot, this rule assumes that 3d is already built.
hashchk-rebuild:
	rm -rf hashchk/3d
	+$(MAKE) -f hashchk.Makefile
	+$(MAKE) hashchk

hashchk-boot: 3d
	+$(MAKE) hashchk-rebuild
