# Tests of the standalone F# hash checker (src/3d/hashchk).
#
# Each test has 3d produce hashes, then checks them with the hash checker.
# The tests in share/everparse/tests/3d check the same hashes, but with 3d
# itself only, so that they do not depend on the hash checker.

EVERPARSE_HOME ?= $(realpath ../../..)
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
export FSTAR_EXE

HASHCHK ?= dotnet $(EVERPARSE_HOME)/src/3d/hashchk/bin/Debug/net10.0/win-x64/everparse-hashchk.dll
export HASHCHK

3D_LOWSTAR=$(EVERPARSE_HOME)/bin/everparse-3d.exe --api lowstar --fstar $(FSTAR_EXE)

# The batch corpus is not copied here: it is the one of
# share/everparse/tests/3d/lowstar, i.e. every non-FAIL .3d file there, as in
# its batch-test.
LOWSTAR_TESTS=$(EVERPARSE_HOME)/share/everparse/tests/3d/lowstar
BATCH_FILES=$(filter-out $(LOWSTAR_TESTS)/FAIL%.3d, $(wildcard $(LOWSTAR_TESTS)/*.3d))

APIS=lowstar pulse

all: hashchk-batch-test hashchk-inplace-hash-test \
	$(addprefix hashchk-modules-,$(APIS)) $(addprefix hashchk-save-hashes-,$(APIS))

# Rebuild the standalone hash checker. We use hashchk-rebuild rather
# than hashchk-boot, because 3d is already built by the time this
# Makefile is run, and rebuilding it here could race with the tests
# currently running it.
.PHONY: hashchk-boot
hashchk-boot:
	+$(MAKE) -C .. hashchk-rebuild

# Each test first produces its hashes with 3d, independently of the hash
# checker, so that both can be built in parallel.

.PHONY: batch-test
batch-test:
	mkdir -p out.batch
	$(3D_LOWSTAR) --odir out.batch --batch --no_copy_everparse_h --save_hashes $(BATCH_FILES)

.PHONY: hashchk-batch-test
hashchk-batch-test: batch-test hashchk-boot
	$(HASHCHK) --api lowstar --odir out.batch --check_hashes strong $(BATCH_FILES)

.PHONY: inplace-hash-test
inplace-hash-test:
	mkdir -p out.inplace-hash
	$(3D_LOWSTAR) --odir out.inplace-hash --batch --no_copy_everparse_h $(LOWSTAR_TESTS)/Comments.3d

.PHONY: hashchk-inplace-hash-test
hashchk-inplace-hash-test: inplace-hash-test hashchk-boot
	$(HASHCHK) --api lowstar --odir out.inplace-hash --check_hashes inplace $(LOWSTAR_TESTS)/Comments.3d
	$(HASHCHK) --api lowstar --check_inplace_hash $(LOWSTAR_TESTS)/Comments.3d=out.inplace-hash/Comments.h

# modules and save_hashes, once per API, each into its own output directory.

define api_tests
.PHONY: modules-$(1) save-hashes-$(1) hashchk-modules-$(1) hashchk-save-hashes-$(1)
modules-$(1):
	+$$(MAKE) -C modules build EVERPARSE_API=$(1)
save-hashes-$(1):
	+$$(MAKE) -C save_hashes build EVERPARSE_API=$(1)
hashchk-modules-$(1): modules-$(1) hashchk-boot
	+$$(MAKE) -C modules hashchk-check EVERPARSE_API=$(1)
hashchk-save-hashes-$(1): save-hashes-$(1) hashchk-boot
	+$$(MAKE) -C save_hashes hashchk-check EVERPARSE_API=$(1)
endef

$(foreach api,$(APIS),$(eval $(call api_tests,$(api))))

clean:
	rm -rf out.batch out.inplace-hash
	+$(MAKE) -C modules clean
	+$(MAKE) -C save_hashes clean

.PHONY: all clean
