deps:

.PHONY: deps

ifeq (,$(OS))
export OS := $(shell uname)
endif

ifeq ($(OS),Windows_NT)
  export CC:=x86_64-w64-mingw32-gcc
  export LD:=x86_64-w64-mingw32-ld
  export AR:=x86_64-w64-mingw32-ar
endif

export EVERPARSE_OPT_PATH := $(realpath opt)
ifeq ($(OS),Windows_NT)
export EVERPARSE_OPT_PATH := $(shell cygpath -m $(EVERPARSE_OPT_PATH))
endif

ifeq (1,$(EVERPARSE_ONLY_3D))
NO_PULSE := 1
endif

EVERPARSE_Z3_VERSION ?= 4.13.3

ifeq (1,$(EVERPARSE_USE_MY_DEPS))
export EVERPARSE_USE_OPAMROOT:=1
export EVERPARSE_USE_FSTAR_EXE:=1
export EVERPARSE_USE_KRML_EXE:=1
export EVERPARSE_USE_PULSE_HOME:=1
endif

NEED_KRML :=
ifneq (1,$(EVERPARSE_USE_KRML_EXE))
ifeq ($(OS),Windows_NT)
export KRML_EXE := $(EVERPARSE_OPT_PATH)/karamel/out/bin/krml.exe
else
export KRML_EXE := $(EVERPARSE_OPT_PATH)/karamel/out/bin/krml
endif
NEED_KRML := $(EVERPARSE_OPT_PATH)/karamel.done
else
export EVERPARSE_USE_FSTAR_EXE:=1
ifeq (,$(KRML_EXE))
# TODO: fix Karamel to not require KRML_HOME set
$(error "Inconsistent setup: EVERPARSE_USE_KRML_EXE set but KRML_EXE not set")
endif
endif

NEED_PULSE :=
ifeq (,$(NO_PULSE))
ifneq (1,$(EVERPARSE_USE_PULSE_HOME))
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
NEED_PULSE := $(EVERPARSE_OPT_PATH)/pulse.done
else
export EVERPARSE_USE_FSTAR_EXE:=1
ifeq (,$(PULSE_HOME))
$(error "Inconsistent setup: EVERPARSE_USE_PULSE_HOME set but PULSE_HOME not set")
endif
endif
endif

NEED_FSTAR :=
ifneq (1,$(EVERPARSE_USE_FSTAR_EXE))
export FSTAR_EXE := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
NEED_FSTAR := $(EVERPARSE_OPT_PATH)/FStar.done
z3_exe := $(shell $(FSTAR_EXE) --locate_z3 \$(EVERPARSE_Z3_VERSION) 2>/dev/null)
ifneq (0,$(.SHELLSTATUS))
z3_exe :=
endif
else
# F* already exists, so we assume its fstar-lib is already compiled
export EVERPARSE_USE_OPAMROOT:=1
ifeq (,$(FSTAR_EXE))
# rely on PATH
export FSTAR_EXE := fstar.exe
endif
endif

NEED_OPAM_DIR :=
NEED_OPAM :=
ifneq (1,$(EVERPARSE_USE_OPAMROOT))
NEED_OPAM_DIR := $(EVERPARSE_OPT_PATH)/opam/opam-init/init.sh
NEED_OPAM := $(EVERPARSE_OPT_PATH)/opam.done
endif
with_opam := eval "$$($(EVERPARSE_OPT_PATH)/opam-env.sh --shell)" &&

NEED_Z3 :=
ifeq (,$(z3_exe))
z3_exe := $(shell which z3-$(EVERPARSE_Z3_VERSION))
ifneq (0,$(.SHELLSTATUS))
z3_exe :=
endif
endif
ifeq (,$(z3_exe))
NEED_Z3 := $(EVERPARSE_OPT_PATH)/z3
ifeq ($(OS),Windows_NT)
z3_dir := $(shell cygpath -u $(NEED_Z3))
else
z3_dir := $(NEED_Z3)
endif
else
NEED_Z3 := 
z3_dir := $(dir $(z3_exe))
ifeq ($(OS),Windows_NT)
z3_dir := $(shell cygpath -u $(z3_dir))
endif
endif
NEED_Z3_TESTGEN := $(NEED_Z3)
ifeq (1,$(ADMIT))
NEED_Z3 :=
endif
export PATH := $(z3_dir):$(PATH)

$(EVERPARSE_OPT_PATH)/opam/opam-init/init.sh:
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) opam

ifeq (,$(filter clean distclean $(clean_rules),$(MAKECMDGOALS)))
opam-env.Makefile: $(NEED_OPAM_DIR)
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
else
-include opam-env.Makefile
endif

# point to the Makefile because Z3 depends on the F* directory only but when I build F* the directory timestamp changes
$(EVERPARSE_OPT_PATH)/FStar/Makefile: $(EVERPARSE_OPT_PATH)/hashes.Makefile
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) FStar/Makefile

$(EVERPARSE_OPT_PATH)/karamel/Makefile: $(EVERPARSE_OPT_PATH)/hashes.Makefile
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) karamel/Makefile

$(EVERPARSE_OPT_PATH)/pulse/Makefile: $(EVERPARSE_OPT_PATH)/hashes.Makefile
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) pulse/Makefile

$(EVERPARSE_OPT_PATH)/opam.done: $(EVERPARSE_OPT_PATH)/opam/opam-init/init.sh $(EVERPARSE_OPT_PATH)/FStar/Makefile $(EVERPARSE_OPT_PATH)/karamel/Makefile $(EVERPARSE_OPT_PATH)/pulse/Makefile
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) opam.done

$(EVERPARSE_OPT_PATH)/FStar.done: $(EVERPARSE_OPT_PATH)/FStar/Makefile $(NEED_OPAM)
	rm -f $@
	+$(with_opam) $(MAKE) -C $(EVERPARSE_OPT_PATH)/FStar ADMIT=1
	touch $@

$(EVERPARSE_OPT_PATH)/z3: $(EVERPARSE_OPT_PATH)/FStar/Makefile
	rm -rf $@ $@.tmp
	mkdir -p $@.tmp
	$(dir $<)/.scripts/get_fstar_z3.sh $@.tmp
	rm -rf $@.tmp/z3-4.8.5
	mv $@.tmp $@
	touch $@

# NOTE: we unset KRML_EXE here so that Karamel's own build (in particular
# krmllib) uses the freshly-built in-tree `krml` (../krml) instead of the
# not-yet-installed $(EVERPARSE_OPT_PATH)/karamel/out/bin/krml that we export
# below for EverParse. Otherwise krmllib's `KRML_EXE ?= ../krml` picks up our
# exported value and fails with "No rule to make target .../out/bin/krml".
$(EVERPARSE_OPT_PATH)/karamel.done: $(EVERPARSE_OPT_PATH)/karamel/Makefile $(NEED_FSTAR) $(NEED_OPAM)
	rm -f $@
	+$(with_opam) env -u KRML_EXE OTHERFLAGS='--admit_smt_queries true' $(MAKE) -C $(EVERPARSE_OPT_PATH)/karamel minimal
	+$(with_opam) env -u KRML_EXE OTHERFLAGS='--admit_smt_queries true' KRML_LIBDIR="$(EVERPARSE_OPT_PATH)/karamel/krmllib" KRML_INCLUDEDIR="$(EVERPARSE_OPT_PATH)/karamel/include" KRML_MISCDIR="$(EVERPARSE_OPT_PATH)/karamel/misc" $(MAKE) -C "$(EVERPARSE_OPT_PATH)/karamel/krmllib"
	+$(with_opam) env -u KRML_EXE $(MAKE) -C "$(EVERPARSE_OPT_PATH)/karamel" _install PREFIX="$(EVERPARSE_OPT_PATH)/karamel/out"
ifeq ($(OS),Windows_NT)
	mv "$(EVERPARSE_OPT_PATH)/karamel/out/bin/krml" "$(EVERPARSE_OPT_PATH)/karamel/out/bin/krml.exe"
endif
	touch $@

$(EVERPARSE_OPT_PATH)/pulse.done: $(EVERPARSE_OPT_PATH)/pulse/Makefile $(NEED_FSTAR) $(NEED_OPAM)
	rm -f $@
	+$(with_opam) $(MAKE) -C $(EVERPARSE_OPT_PATH)/pulse ADMIT=1
	touch $@

env:
ifeq ($(OS),Windows_NT)
	@echo export CC=$(CC)
	@echo export LD=$(LD)
	@echo export AR=$(AR)
endif
	@echo export EVERPARSE_USE_OPAMROOT=$(EVERPARSE_USE_OPAMROOT)
	@echo export EVERPARSE_USE_FSTAR_EXE=$(EVERPARSE_USE_FSTAR_EXE)
	@echo export EVERPARSE_USE_KRML_EXE=$(EVERPARSE_USE_KRML_EXE)
	@echo export EVERPARSE_USE_PULSE_HOME=$(EVERPARSE_USE_PULSE_HOME)
	@echo export FSTAR_EXE=$(FSTAR_EXE)
	@echo export KRML_EXE=$(KRML_EXE)
ifeq (,$(NO_PULSE))
	@echo export PULSE_HOME=$(PULSE_HOME)
endif
ifeq ($(OS),Windows_NT)
	@echo export EVERPARSE_HOME=$(shell cygpath -u $(CURDIR))
else
	@echo export EVERPARSE_HOME=$(CURDIR)
endif
	@echo export EVERPARSE_Z3_VERSION=$(EVERPARSE_Z3_VERSION)
	@echo export PATH=\"$(z3_dir):'$$PATH'\"

.PHONY: env

deps: $(NEED_OPAM) $(NEED_FSTAR) $(NEED_Z3) $(NEED_KRML) $(NEED_PULSE)

.PHONY: deps

distclean: clean
	rm -rf opam-env.Makefile
	+$(MAKE) -C opt clean

clean:

.PHONY: clean distclean
