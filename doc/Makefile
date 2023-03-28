# Minimal makefile for Sphinx documentation
#

all: html 3d

export EVERPARSE_HOME?=$(realpath ..)

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    # fstar.exe not found in PATH, assuming Everest source tree
    FSTAR_HOME=$(realpath $(EVERPARSE_HOME)/../FStar)
  else
    # fstar.exe found in PATH, assuming directory ending with /bin
    FSTAR_HOME=$(realpath $(dir $(FSTAR_EXE))/..)
  endif
  export FSTAR_HOME
endif

export KRML_HOME?=$(realpath $(EVERPARSE_HOME)/../karamel)

3D=$(EVERPARSE_HOME)/bin/3d.exe
3D_EXCLUDE=ConstColor.3d
3D_CONFIG=Arch.3d.config
3D_FILES_WITH_CONFIG=PointArch_32_64.3d
3D_FILES=$(filter-out $(3D_EXCLUDE) $(3D_FILES_WITH_CONFIG),$(wildcard *.3d))
3D_MODULES=$(basename $(3D_FILES) $(3D_FILES_WITH_CONFIG))
3D_MODULES_AND_WRAPPERS=$(3D_MODULES) $(addsuffix Wrapper,$(3D_MODULES))
3D_C_AND_H_FILES=$(filter-out BaseWrapper.c BaseWrapper.h,$(addsuffix .c,$(3D_MODULES_AND_WRAPPERS)) $(addsuffix .h,$(3D_MODULES_AND_WRAPPERS)))
3D_DIFF=$(addsuffix .diff,$(3D_C_AND_H_FILES))
3D_OUT=$(addprefix out/,$(3D_C_AND_H_FILES))
3D_SNAPSHOT=$(addprefix 3d-snapshot/,$(3D_C_AND_H_FILES))
AUX_HEADERS=GetFieldPtrBase.h

# You can set these variables from the command line.
SPHINXOPTS    = -W
SPHINXBUILD   = sphinx-build
SPHINXPROJ    = EverParseDoc
SOURCEDIR     = .
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile test all 3d clean 3d-do-tests 3d-do-interpreter-tests %.diff 3d-snapshot 3d-ci %.diff-nobuild

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

3d: 3d-do-tests

3d-ci:  $(3D_DIFF)

3d-do-tests:
	mkdir -p out
	$(3D) --odir out --batch $(3D_FILES)
	$(3D) --odir out --batch $(3D_FILES_WITH_CONFIG) --config $(3D_CONFIG)
	cp $(AUX_HEADERS) out
	+$(MAKE) -C out -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers' test

3d-do-interpreter-tests:
	mkdir -p interpret.out
	$(3D) --odir interpret.out --batch $(3D_FILES) --interpret
	$(3D) --odir interpret.out --batch $(3D_FILES_WITH_CONFIG) --config $(3D_CONFIG) --interpret
	cp $(AUX_HEADERS) interpret.out
	+$(MAKE) -C interpret.out -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers' test

$(3D_OUT): out/%: 3d-do-tests

$(3D_SNAPSHOT): 3d-snapshot/%: out/%
	mkdir -p 3d-snapshot
	if diff -w -B $^ $@ ; then touch $@ ; else cp $^ $@ ; fi

3d-snapshot: $(3D_SNAPSHOT)

all-diffs: $(3D_DIFF)

%.diff: 3d-do-tests
	diff -w -B out/$(basename $@) 3d-snapshot/$(basename $@)

all-diffs-nobuild: $(addsuffix -nobuild, $(3D_DIFF))

%.diff-nobuild:
	diff -w -B out/$(basename $@) 3d-snapshot/$(basename $@)

%.accept:
	cp  out/$(basename $@) 3d-snapshot/$(basename $@)
clean:
	rm -rf out _build
