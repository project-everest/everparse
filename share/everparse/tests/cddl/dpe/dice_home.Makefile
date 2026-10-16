echo_DICE_HOME:

.PHONY: echo_DICE_HOME

ifeq (,$(EVERPARSE_HOME))
EVERPARSE_HOME := $(realpath ../../../../..)
endif
include $(EVERPARSE_HOME)/lib/everparse/windows.Makefile

clean_rules += clean-dice

ifeq ($(OS),Windows_NT)
    local_curdir := $(shell cygpath -m "$(CURDIR)")
else
    local_curdir := $(CURDIR)
endif

ifeq (,$(DICE_HOME))

ifneq (,$(wildcard $(EVERPARSE_HOME)/opt/FStar/pulse/share/pulse/examples/dice/.))

export DICE_HOME := $(EVERPARSE_HOME)/opt/FStar/pulse/share/pulse/examples/dice

else

dice_fstar := $(local_curdir)/dice
export DICE_HOME := $(dice_fstar)/pulse/share/pulse/examples/dice

FStar_repo=https://github.com/FStarLang/FStar
ifeq (,$(FSTAR_EXE))
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
endif

dice.done:
	test -d "$(dice_fstar)" || { \
	  fstar_version=$$("$(FSTAR_EXE)" --version) && \
	  fstar_hash=$$(printf '%s\n' "$$fstar_version" | sed -n 's/^commit=//p' | tr -d '\r') && \
	  { test -n "$$fstar_hash" || { echo "Unable to determine F* commit from --version" >&2; exit 1; }; } && \
	  rm -rf "$(dice_fstar)".tmp && \
	  git clone --no-checkout --filter=blob:none $(FStar_repo) "$(dice_fstar)".tmp && \
	  cd "$(dice_fstar)".tmp && \
	  git sparse-checkout init --no-cone && \
	  git sparse-checkout set --no-cone '!/*' '!/.*' && \
	  git sparse-checkout add pulse/share/pulse/examples/dice && \
	  git checkout "$$fstar_hash" && \
	  cd .. && mv "$(dice_fstar)".tmp "$(dice_fstar)"; \
	}
	touch $@

NEED_DICE := dice.done

endif

endif

echo_DICE_HOME:
	@echo "$(DICE_HOME)"

clean-dice:
	rm -rf dice.done $(local_curdir)/dice

.PHONY: clean-dice
