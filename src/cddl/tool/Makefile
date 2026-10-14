all: build

EVERPARSE_HOME := $(realpath ../../..)
include $(EVERPARSE_HOME)/src/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/cbor/spec $(EVERPARSE_HOME)/lib/everparse/cddl/spec $(EVERPARSE_HOME)/lib/everparse/cddl/pulse $(EVERPARSE_HOME)/lib/everparse/cbor/pulse

ALREADY_CACHED := *,-CDDL.Tool,

clean_rules += clean-ocaml clean-done

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

ocaml.done: $(ALL_CHECKED_FILES)
	rm -f $@
	+$(MAKE) -f $(basename $@).Makefile
	touch $@

EVERPARSE_CDDL=$(EVERPARSE_HOME)/bin/cddl.exe

# evercddl.lib is a build-time artifact of cddl.exe, not something EverParse
# ships: its only consumer is the roundtrip test, which links against it to
# compare the OCaml parser with the extracted F* AST. So install it into that
# test's own directory rather than under the $(EVERPARSE_HOME) prefix.
EVERCDDL_LIB_PREFIX=$(EVERPARSE_HOME)/src/cddl/tests/roundtrip/evercddl

build: $(EVERPARSE_CDDL)

.PHONY: build

$(EVERPARSE_CDDL): ocaml.done $(wildcard ocaml/*/*.ml*)
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build
	rm -rf $(EVERCDDL_LIB_PREFIX)
	cd ocaml && dune install --prefix=$(EVERCDDL_LIB_PREFIX) --section=lib evercddl
	mkdir -p $(dir $@)
	cp ocaml/_build/install/default/bin/cddl.exe $@
	chmod +w $@ # because dune produces read-only executables

.PHONY: all

clean-ocaml:
	if which dune ; then cd ocaml && dune clean ; fi

.PHONY: clean-ocaml

clean-done:
	rm -f *.depend *.depend.rsp *.done
	rm -rf ocaml/evercddl-lib/extracted
	rm -rf $(EVERCDDL_LIB_PREFIX)

.PHONY: clean-done
