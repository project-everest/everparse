deps:

.PHONY: deps

ifeq (,$(OS))
export OS := $(shell uname)
endif

export EVERPARSE_OPT_PATH := $(realpath opt)
ifeq ($(OS),Windows_NT)
export EVERPARSE_OPT_PATH := $(shell cygpath -m $(EVERPARSE_OPT_PATH))
# Pulse does not compile on Windows
NO_PULSE := 1
endif

# config.Makefile records the dependency configuration (whether to build
# F*, Karamel and opam from source or to use pre-existing ones). It is
# produced by ./configure (see ./configure --help). The rule below has no
# prerequisites and invokes ./configure without argument, so that a default
# config.Makefile is produced on first use.
ifeq (,$(filter clean distclean $(clean_rules),$(MAKECMDGOALS)))
config.Makefile:
	./configure
include config.Makefile
else
-include config.Makefile
endif

export EVERPARSE_USE_FSTAR_EXE
export EVERPARSE_USE_KRML_EXE
export EVERPARSE_USE_OPAMROOT

# DICE_HOME (directory holding the Pulse DICE examples) may be set by
# config.Makefile (via ./configure --dice-home) and otherwise defaults to
# the from-source location below. Export it so the cddl DPE tests pick it up.
export DICE_HOME

include src/z3-version.Makefile

NEED_KRML :=
ifneq (1,$(EVERPARSE_USE_KRML_EXE))
export KRML_EXE := $(EVERPARSE_OPT_PATH)/FStar/karamel/out/bin/krml
NEED_KRML := $(EVERPARSE_OPT_PATH)/karamel.done
else
ifeq (,$(KRML_EXE))
# TODO: fix Karamel to not require KRML_HOME set
$(error "Inconsistent setup: EVERPARSE_USE_KRML_EXE set but KRML_EXE not set")
endif
export KRML_EXE
endif

NEED_FSTAR :=
ifneq (1,$(EVERPARSE_USE_FSTAR_EXE))
export FSTAR_EXE := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
# When building F* from source, the Pulse DICE examples live under opt/.
# config.Makefile (via --dice-home) may have set DICE_HOME already; only
# fall back to this default when it has not.
ifeq (,$(DICE_HOME))
DICE_HOME := $(EVERPARSE_OPT_PATH)/FStar/pulse/share/pulse/examples/dice
endif
NEED_FSTAR := $(EVERPARSE_OPT_PATH)/FStar.done
z3_exe := $(shell $(FSTAR_EXE) --locate_z3 \$(EVERPARSE_Z3_VERSION) 2>/dev/null)
ifneq (0,$(.SHELLSTATUS))
z3_exe :=
endif
else
ifeq (,$(FSTAR_EXE))
# rely on PATH
export FSTAR_EXE := fstar.exe
endif
export FSTAR_EXE
endif

NEED_OPAM_DIR :=
NEED_OPAM :=
ifneq (1,$(EVERPARSE_USE_OPAMROOT))
NEED_OPAM_DIR := $(EVERPARSE_OPT_PATH)/opam/opam-init/init.sh
NEED_OPAM := $(EVERPARSE_OPT_PATH)/opam.done
else
# OPAMROOT may be set (e.g. by config.Makefile) to select the opam root;
# export it so opam-env.sh picks it up. If empty, opam-env.sh falls back
# to the ambient opam root.
export OPAMROOT
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

clean_rules += clean-krmllib

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

$(EVERPARSE_OPT_PATH)/FStar/karamel/Makefile: $(EVERPARSE_OPT_PATH)/FStar/Makefile $(EVERPARSE_OPT_PATH)/hashes.Makefile
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) FStar/karamel/Makefile

$(EVERPARSE_OPT_PATH)/opam.done: $(EVERPARSE_OPT_PATH)/opam/opam-init/init.sh
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) opam.done

# F*'s OCaml build dependencies (fstar-deps.opam, derived from F*'s own
# opam file) are installed as part of building F* from source, rather than
# when populating the opam root. This keeps opam-root creation independent
# of the F* sources. With an ambient opam root the user is responsible for
# providing these dependencies, matching the opam.done convention above.
$(EVERPARSE_OPT_PATH)/fstar-deps.opam: $(EVERPARSE_OPT_PATH)/FStar/Makefile
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) fstar-deps.opam

ifneq (1,$(EVERPARSE_USE_OPAMROOT))
install_fstar_deps := $(with_opam) env OPAMYES=1 OPAMNODEPEXTS=1 opam install --deps-only $(EVERPARSE_OPT_PATH)/fstar-deps.opam
else
install_fstar_deps := @echo "Using ambient opam root: assuming F* OCaml dependencies are already installed"
endif

$(EVERPARSE_OPT_PATH)/FStar.done: $(EVERPARSE_OPT_PATH)/FStar/Makefile $(EVERPARSE_OPT_PATH)/fstar-deps.opam $(NEED_OPAM)
	rm -f $@
	$(install_fstar_deps)
	+$(with_opam) $(MAKE) -C $(EVERPARSE_OPT_PATH)/FStar ADMIT=1
	touch $@

$(EVERPARSE_OPT_PATH)/z3: $(EVERPARSE_OPT_PATH)/FStar/Makefile
	rm -rf $@ $@.tmp
	mkdir -p $@.tmp
	$(dir $<)/.scripts/get_fstar_z3.sh $@.tmp
	rm -rf $@.tmp/z3-4.8.5
	mv $@.tmp $@
	touch $@

$(EVERPARSE_OPT_PATH)/karamel.done: $(EVERPARSE_OPT_PATH)/FStar/karamel/Makefile $(NEED_FSTAR) $(NEED_OPAM)
	rm -f $@
	+$(with_opam) env OTHERFLAGS='--admit_smt_queries true' $(MAKE) -C $(EVERPARSE_OPT_PATH)/FStar/karamel minimal
	touch $@

krmllib.done: $(NEED_KRML)
	# Needed by LowParse (Pulse) tests
	+export KRML_LIBPATH="$$($(KRML_EXE) -locate-krmllib)" && $(MAKE) -C "$$KRML_LIBPATH"/dist/generic -f Makefile.basic
	touch $@

# Install the F* application library (fstar.lib) and its OCaml dependencies
# into the opam switch used by EverParse. This is needed by every leaf rule
# that links F*-extracted OCaml against fstar.lib (e.g. the 3d, ASN1 and cddl
# tools). With a binary F* package, fstar.lib is not available until installed
# here; with a source build, $(NEED_FSTAR) (FStar.done) rebuilds F* first.
fstarlib.done: $(NEED_FSTAR) $(NEED_OPAM)
	rm -f $@
	$(with_opam) $(FSTAR_EXE) --install_lib_with_deps
	touch $@

env:
	@echo export EVERPARSE_USE_OPAMROOT=$(EVERPARSE_USE_OPAMROOT)
	@echo export EVERPARSE_USE_FSTAR_EXE=$(EVERPARSE_USE_FSTAR_EXE)
	@echo export EVERPARSE_USE_KRML_EXE=$(EVERPARSE_USE_KRML_EXE)
	@echo export FSTAR_EXE=$(FSTAR_EXE)
	@echo export DICE_HOME=$(DICE_HOME)
	@echo export KRML_EXE=$(KRML_EXE)
ifeq ($(OS),Windows_NT)
	@echo export EVERPARSE_HOME=$(shell cygpath -u $(CURDIR))
else
	@echo export EVERPARSE_HOME=$(CURDIR)
endif
	@echo export EVERPARSE_Z3_VERSION=$(EVERPARSE_Z3_VERSION)
	@echo export PATH=\"$(z3_dir):'$$PATH'\"

.PHONY: env

deps: $(NEED_OPAM) $(NEED_FSTAR) $(NEED_Z3) $(NEED_KRML)

deps: krmllib.done fstarlib.done

.PHONY: deps

clean-krmllib:
	rm -f krmllib.done
	# +$(MAKE) -C "$$($(KRML_EXE) -locate-krmllib)"/dist/generic -f Makefile.basic clean || true # This works, but I am not sure we should clean up anything outside of the EverParse tree. In the opt/ case, krmllib is in opt/FStar, which `distclean` will remove altogether.

.PHONY: clean-krmllib

distclean: clean clean-krmllib
	rm -rf opam-env.Makefile config.Makefile fstarlib.done opt/fstar-bin-package
	+$(MAKE) -C opt clean

clean:

.PHONY: clean distclean
