deps:

.PHONY: deps

# Include specific options on release branches (e.g. EVERPARSE_OPAM_REPOSITORY)
-include release.Makefile

ifeq (,$(OS))
export OS := $(shell uname)
endif
ifneq ($(OS),Windows_NT)
package-subset: cddl
endif
ifneq ($(OS),Darwin)
all: cose
endif

export EVERPARSE_OPT_PATH := $(realpath opt)
ifeq ($(OS),Windows_NT)
export EVERPARSE_OPT_PATH := $(shell cygpath -m $(EVERPARSE_OPT_PATH))
# Pulse does not compile on Windows
NO_PULSE := 1
endif

$(EVERPARSE_OPT_PATH)/everest:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

ifeq (,$(OPAMNODEPEXTS))
export OPAMNODEPEXTS := 1
endif
ifeq (,$(OPAMYES))
export OPAMYES := 1
endif

cygwin_local_install :=
ifeq ($(OS),Windows_NT)
cygwin_local_install += --cygwin-local-install
endif

$(EVERPARSE_OPT_PATH)/opam: $(EVERPARSE_OPT_PATH)/everest
	rm -rf $@ $@.tmp
	if ! { opam init $(cygwin_local_install) --no-setup --root=$(EVERPARSE_OPT_PATH)/opam --compiler=5.3.0 $(EVERPARSE_OPAM_REPOSITORY) && eval "$$(opam env --root=$(EVERPARSE_OPT_PATH)/opam --set-root)" && bash $(EVERPARSE_OPT_PATH)/everest/everest opam ; } ; then mv $@ $@.tmp ; exit 1 ; fi
	touch $@

NEED_OPAM :=
ifeq (,$(EVERPARSE_USE_OPAMROOT))
NEED_OPAM := $(EVERPARSE_OPT_PATH)/opam
with_opam := eval "$$(opam env --root="$(EVERPARSE_OPT_PATH)/opam" --set-root)" &&
endif

Z3_VERSION := 4.13.3

NEED_FSTAR :=
ifeq (,$(FSTAR_EXE))
export FSTAR_EXE := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
NEED_FSTAR := $(FSTAR_EXE)
z3_exe := $(shell $(FSTAR_EXE) --locate_z3 \$(Z3_VERSION) 2>/dev/null)
else
# F* already exists, so we assume its fstar-lib is already compiled
NEED_OPAM :=
endif

NEED_KRML :=
ifeq (,$(KRML_HOME))
export KRML_HOME := $(EVERPARSE_OPT_PATH)/karamel
NEED_KRML := $(KRML_HOME)/_build/default/src/Karamel.exe
else
ifneq (,$(NEED_FSTAR))
$(error "Inconsistent setup: KRML_HOME set but FSTAR_EXE not set")
endif
endif

NEED_PULSE :=
ifeq (,$(NO_PULSE))
ifeq (,$(PULSE_HOME))
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
NEED_PULSE := $(PULSE_HOME)
else
ifneq (,$(NEED_FSTAR))
$(error "Inconsistent setup: PULSE_HOME set but FSTAR_EXE not set")
endif
endif
endif

ifeq (,$(z3_exe))
z3_exe := $(shell which z3-$(Z3_VERSION))
ifneq (0,$(.SHELLSTATUS))
z3_exe :=
endif
endif
ifeq (,$(z3_exe))
NEED_Z3 := $(EVERPARSE_OPT_PATH)/z3
ifeq ($(OS),Windows_NT)
export PATH := $(shell cygpath -u $(NEED_Z3)):$(PATH)
else
export PATH := $(NEED_Z3):$(PATH)
endif
else
NEED_Z3 := 
endif
ifeq (1,$(ADMIT))
OTHERFLAGS += --admit_smt_queries true
export OTHERFLAGS
NEED_Z3 :=
endif

opam-env.Makefile: $(NEED_OPAM)
	rm -rf $@.tmp
	$(EVERPARSE_OPT_PATH)/opam-env.sh > $@.tmp
	echo >> $@.tmp
	echo env: opam-env >> $@.tmp
	echo .PHONY: opam-env >> $@.tmp
	echo opam-env: >> $@.tmp
	echo "	\"$(EVERPARSE_OPT_PATH)\"/opam-env.sh --shell" >> $@.tmp
	mv $@.tmp $@
	touch $@

include opam-env.Makefile

$(EVERPARSE_OPT_PATH)/FStar:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

$(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe: $(EVERPARSE_OPT_PATH)/FStar $(NEED_OPAM)
	+$(with_opam) $(MAKE) -C $< ADMIT=1
	touch $@

$(EVERPARSE_OPT_PATH)/z3: $(EVERPARSE_OPT_PATH)/FStar
	rm -rf $@ $@.tmp
	mkdir -p $@.tmp
	$</.scripts/get_fstar_z3.sh $@.tmp
	rm -rf $@.tmp/z3-4.8.5
	mv $@.tmp $@
	touch $@

$(EVERPARSE_OPT_PATH)/karamel:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

$(EVERPARSE_OPT_PATH)/karamel/_build/default/src/Karamel.exe: $(EVERPARSE_OPT_PATH)/karamel $(NEED_FSTAR) $(NEED_OPAM)
	+$(with_opam) env OTHERFLAGS='--admit_smt_queries true' $(MAKE) -C $<
	touch $@

$(EVERPARSE_OPT_PATH)/pulse:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

$(EVERPARSE_OPT_PATH)/pulse/out: $(EVERPARSE_OPT_PATH)/pulse $(NEED_FSTAR) $(NEED_OPAM)
	+$(with_opam) $(MAKE) -C $< ADMIT=1
	touch $@

env:
	@echo export FSTAR_EXE=$(FSTAR_EXE)
	@echo export KRML_HOME=$(KRML_HOME)
ifeq (,$(NO_PULSE))
	@echo export PULSE_HOME=$(PULSE_HOME)
endif
ifeq ($(OS),Windows_NT)
	@echo export EVERPARSE_HOME=$(shell cygpath -u $(CURDIR))
	@echo export PATH=$(shell cygpath -u $(EVERPARSE_OPT_PATH))/FStar/bin:$(shell cygpath -u $(EVERPARSE_OPT_PATH))/z3:\"'$$PATH'\"
else
	@echo export EVERPARSE_HOME=$(CURDIR)
	@echo export PATH=$(EVERPARSE_OPT_PATH)/FStar/bin:$(EVERPARSE_OPT_PATH)/z3:\"'$$PATH'\"
endif

.PHONY: env

deps: $(NEED_OPAM) $(NEED_FSTAR) $(NEED_Z3) $(NEED_KRML) $(NEED_PULSE)

.PHONY: deps
