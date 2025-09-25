all: build extraction-all

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse $(EVERPARSE_SRC_PATH)/cbor/pulse

ALREADY_CACHED := *,-CDDL.Tool,

clean_rules += c.clean rust.clean clean-ocaml clean-done

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

ocaml.done: $(ALL_CHECKED_FILES)
	rm -f $@
	+$(MAKE) -f $(basename $@).Makefile
	touch $@

plugin.done: $(ALL_CHECKED_FILES)
	rm -f $@
	+$(MAKE) -f $(basename $@).Makefile
	touch $@

EVERPARSE_CDDL=$(EVERPARSE_SRC_PATH)/../bin/cddl.exe

build: $(EVERPARSE_CDDL)

.PHONY: build

$(EVERPARSE_CDDL): ocaml.done plugin.done $(wildcard ocaml/*/*.ml*)
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build
	cd ocaml && dune install --prefix=$(realpath $(EVERPARSE_SRC_PATH)/..)

.PHONY: all

extraction-c: $(ALL_CHECKED_FILES)
	$(MAKE) -f $@.Makefile

extraction-rust: $(ALL_CHECKED_FILES)
	$(MAKE) -f $@.Makefile

extraction-all: extraction-c extraction-rust

.PHONY: extraction extraction-c extraction-rust extraction-all

%.clean:
	rm -rf extraction-$(basename $@)

.PHONY: %.clean

clean-ocaml:
	if which dune ; then cd ocaml && dune clean ; fi

.PHONY: clean-ocaml

clean-done:
	rm -f *.depend *.depend.rsp *.done
	rm -rf ocaml/evercddl-lib/extracted ocaml/evercddl-plugin/extracted

.PHONY: clean-done
