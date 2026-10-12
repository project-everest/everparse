all: build

EVERPARSE_HOME := $(realpath ../../..)
include $(EVERPARSE_HOME)/src/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_HOME)/src/cbor/spec $(EVERPARSE_HOME)/src/cddl/spec $(EVERPARSE_HOME)/src/cddl/pulse $(EVERPARSE_HOME)/src/cbor/pulse

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

build: $(EVERPARSE_CDDL)

.PHONY: build

$(EVERPARSE_CDDL): ocaml.done $(wildcard ocaml/*/*.ml*)
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build
	cd ocaml && dune install --prefix=$(EVERPARSE_HOME)

.PHONY: all

clean-ocaml:
	if which dune ; then cd ocaml && dune clean ; fi

.PHONY: clean-ocaml

clean-done:
	rm -f *.depend *.depend.rsp *.done
	rm -rf ocaml/evercddl-lib/extracted

.PHONY: clean-done
