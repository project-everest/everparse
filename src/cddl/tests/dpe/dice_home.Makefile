echo_DICE_HOME:

.PHONY: echo_DICE_HOME

ifeq (,$(EVERPARSE_SRC_PATH))
EVERPARSE_SRC_PATH := $(realpath ../../..)
include $(EVERPARSE_SRC_PATH)/windows.Makefile
endif

clean_rules += clean-dice

ifeq ($(OS),Windows_NT)
    local_curdir := $(shell cygpath -m "$(CURDIR)")
else
    local_curdir := $(CURDIR)
endif

ifeq (,$(DICE_HOME))

dice_fstar := $(local_curdir)/dice
export DICE_HOME := $(dice_fstar)/pulse/share/pulse/examples/dice

FStar_repo=https://github.com/FStarLang/FStar
include $(EVERPARSE_SRC_PATH)/../opt/hashes.Makefile

dice.done:
	test -d "$(dice_fstar)" || { rm -rf "$(dice_fstar)".tmp && git clone --no-checkout --filter=blob:none $(FStar_repo) "$(dice_fstar)".tmp && pushd "$(dice_fstar)".tmp && git sparse-checkout init --no-cone && git sparse-checkout set --no-cone '!/*' '!/.*' && git sparse-checkout add pulse/share/pulse/examples/dice && git checkout $(FStar_hash) && popd && mv "$(dice_fstar)".tmp "$(dice_fstar)"; }
	touch $@

NEED_DICE := dice.done

endif

echo_DICE_HOME:
	@echo "$(DICE_HOME)"

clean-dice:
	rm -rf dice.done $(local_curdir)/dice

.PHONY: clean-dice
