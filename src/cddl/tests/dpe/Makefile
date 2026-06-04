all: dpe

EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)

# DICE_HOME holds the Pulse DICE examples. It may be set by ./configure
# (--dice-home) or by deps.Makefile; otherwise it defaults to the from-source
# location under opt/. Export it so the dice/dpe sub-makes use the same value.
ifeq (,$(DICE_HOME))
DICE_HOME := $(EVERPARSE_PATH)/opt/FStar/pulse/share/pulse/examples/dice
endif
export DICE_HOME

# Where to fetch the DICE examples from when DICE_HOME does not exist (e.g.
# when using a F* binary package, which does not ship the Pulse examples).
FSTAR_REPO ?= https://github.com/FStarLang/FStar
DICE_SUBPATH := pulse/share/pulse/examples/dice

OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

clean_rules += clean-test dpe.clean util.clean

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(OUTPUT_DIRECTORY)/CDDLTest.Test.fst: dpe.cddl dpe_postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(OUTPUT_DIRECTORY) --fstar_only $(CDDL_ADMIT)
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

clean-test:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-test

dpe: $(ALL_CHECKED_FILES) dice util | $(DICE_HOME)
	+$(MAKE) -C $@

util:
	+$(MAKE) -C $@

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean

# The Pulse DPE Makefile cannot be used outside of the Pulse
# repository, so we need to build it by hand
dice: | $(DICE_HOME)
	+$(MAKE) -f dice.Makefile

# When DICE_HOME does not exist (e.g. when using a F* binary package, which
# does not ship the Pulse examples), populate it with a partial clone of the
# F* repository: treeless (--filter=tree:0), shallow (--depth 1) and sparse
# (only the DICE examples subtree), at the exact commit reported by
# $(FSTAR_EXE) --version, so that the examples match the F* in use.
$(DICE_HOME):
	commit=`$(FSTAR_EXE) --version | sed -n 's/^commit=//p'` ; \
	if test -z "$$commit" ; then echo "dpe: cannot determine the F* commit from '$(FSTAR_EXE) --version'" >&2 ; exit 1 ; fi ; \
	tmp=`mktemp -d` ; \
	trap "rm -rf $$tmp" EXIT ; \
	git init -q "$$tmp" ; \
	git -C "$$tmp" remote add origin $(FSTAR_REPO) ; \
	git -C "$$tmp" sparse-checkout init --cone ; \
	git -C "$$tmp" sparse-checkout set $(DICE_SUBPATH) ; \
	git -C "$$tmp" fetch -q --depth 1 --filter=tree:0 origin "$$commit" ; \
	git -C "$$tmp" checkout -q FETCH_HEAD ; \
	mkdir -p `dirname "$(DICE_HOME)"` ; \
	mv "$$tmp/$(DICE_SUBPATH)" "$(DICE_HOME)"

.PHONY: dpe dice util
