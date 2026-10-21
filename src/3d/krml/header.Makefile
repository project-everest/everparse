all: headers

EVERPARSE_HOME := $(realpath ../../..)
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
LIB_3D_HOME := $(EVERPARSE_HOME)/lib/everparse/3d
KRML_DIR := $(LIB_3D_HOME)/krml

PYTHON ?= python3
RUNTIME_HEADER_GENERATOR ?= karamel
CUSTARD_HEADER_BUILD ?= $(KRML_DIR)/.custard
CUSTARD_DEPENDENCY_CACHE ?=
CUSTARD_HEADER_JOBS ?= 4
PROFILES := buffer extern static lowstar/buffer lowstar/extern lowstar/static
HEADER_FILES := $(addsuffix /EverParse.h,$(addprefix $(KRML_DIR)/,$(PROFILES)))
COMPANION_FILES := $(addsuffix /EverParseStreamPrimitives.h,$(addprefix $(KRML_DIR)/,static lowstar/static))
RUNTIME_HEADER_SETTINGS := $(KRML_DIR)/.runtime-header-settings

$(RUNTIME_HEADER_SETTINGS): FORCE
	mkdir -p $(KRML_DIR)
	printf '%s\n' "$(RUNTIME_HEADER_GENERATOR)" "$(FSTAR_EXE)" "$(FSTAR_OPTIONS) $(OTHERFLAGS)" > $@.tmp
	cmp -s $@.tmp $@ || mv $@.tmp $@
	rm -f $@.tmp

$(COMPANION_FILES): $(KRML_DIR)/%/EverParseStreamPrimitives.h: runtime_headers.py runtime-contract.json runtime-abi.json
	$(PYTHON) runtime_headers.py --profile $* --companion-only --output $@

ifeq (custard,$(RUNTIME_HEADER_GENERATOR))

HEADER_SOURCES := $(wildcard $(LIB_3D_HOME)/*.fst $(LIB_3D_HOME)/*.fsti)
HEADER_SOURCES += $(wildcard $(EVERPARSE_HOME)/lib/everparse/lowparse/*.fst $(EVERPARSE_HOME)/lib/everparse/lowparse/*.fsti)

$(HEADER_FILES): $(KRML_DIR)/%/EverParse.h: $(HEADER_SOURCES) runtime_headers.py runtime-contract.json header.Makefile $(RUNTIME_HEADER_SETTINGS) $(wildcard $(FSTAR_EXE))
	$(PYTHON) runtime_headers.py --profile $* \
	  --build-dir $(CUSTARD_HEADER_BUILD)/$* --output $@ \
	  --fstar "$(FSTAR_EXE)" --fstar-options "$(FSTAR_OPTIONS) $(OTHERFLAGS)" \
	  $(if $(CUSTARD_DEPENDENCY_CACHE),--dependency-cache "$(CUSTARD_DEPENDENCY_CACHE)") \
	  --jobs $(CUSTARD_HEADER_JOBS)

$(KRML_DIR)/static/EverParse.h: $(KRML_DIR)/static/EverParseStreamPrimitives.h
$(KRML_DIR)/lowstar/static/EverParse.h: $(KRML_DIR)/lowstar/static/EverParseStreamPrimitives.h

headers: $(HEADER_FILES) $(COMPANION_FILES)

else ifeq (karamel,$(RUNTIME_HEADER_GENERATOR))

headers: $(COMPANION_FILES) $(RUNTIME_HEADER_SETTINGS)
	+$(MAKE) -f header-karamel.Makefile RUNTIME_HEADER_SETTINGS="$(RUNTIME_HEADER_SETTINGS)" headers

else
$(error RUNTIME_HEADER_GENERATOR must be custard or karamel)
endif

check-headers: headers
	$(PYTHON) test_runtime_headers.py
	$(PYTHON) check_runtime_headers.py --headers $(KRML_DIR) \
	  --build-dir $(CUSTARD_HEADER_BUILD)/consumers \
	  $(if $(filter 1,$(EVERPARSE_TEST_32BIT)),--32bit) \
	  $(if $(filter 1,$(SANITIZE)),--sanitize)

clean-headers:
	rm -f $(HEADER_FILES) $(COMPANION_FILES) $(RUNTIME_HEADER_SETTINGS) $(RUNTIME_HEADER_SETTINGS).tmp

FORCE:

.PHONY: all headers check-headers clean-headers FORCE
