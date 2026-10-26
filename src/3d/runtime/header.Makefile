all: headers

EVERPARSE_HOME := $(realpath ../../..)
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
LIB_3D_HOME := $(EVERPARSE_HOME)/lib/everparse/3d
RUNTIME_DIR := $(LIB_3D_HOME)/runtime

PYTHON ?= python3
CUSTARD_HEADER_BUILD ?= $(RUNTIME_DIR)/.custard
CUSTARD_HEADER_JOBS ?= 4
PROFILES := buffer extern static lowstar/buffer lowstar/extern lowstar/static
HEADER_FILES := $(addsuffix /EverParse.h,$(addprefix $(RUNTIME_DIR)/,$(PROFILES)))
CUI_FILES := $(HEADER_FILES:.h=.cui)
COMPANION_FILES := $(addsuffix /EverParseStreamPrimitives.h,$(addprefix $(RUNTIME_DIR)/,extern static lowstar/extern lowstar/static))
RUNTIME_HEADER_SETTINGS := $(RUNTIME_DIR)/.runtime-header-settings

$(RUNTIME_HEADER_SETTINGS): FORCE
	mkdir -p $(RUNTIME_DIR)
	printf '%s\n' "Custard C" "$(FSTAR_EXE)" "$(FSTAR_OPTIONS) $(OTHERFLAGS)" > $@.tmp
	cmp -s $@.tmp $@ || mv $@.tmp $@
	rm -f $@.tmp

$(COMPANION_FILES): $(RUNTIME_DIR)/%/EverParseStreamPrimitives.h: runtime_headers.py runtime-contract.json runtime-abi.json
	$(PYTHON) runtime_headers.py --profile $* --companion-only --output $@

HEADER_SOURCES := $(wildcard $(LIB_3D_HOME)/*.fst $(LIB_3D_HOME)/*.fsti)
HEADER_SOURCES += $(wildcard $(EVERPARSE_HOME)/lib/everparse/lowparse/*.fst $(EVERPARSE_HOME)/lib/everparse/lowparse/*.fsti)

define profile_rule
$(RUNTIME_DIR)/$(1)/EverParse.h $(RUNTIME_DIR)/$(1)/EverParse.cui &: $(HEADER_SOURCES) runtime_headers.py runtime-contract.json header.Makefile $(RUNTIME_HEADER_SETTINGS) $(wildcard $(FSTAR_EXE)) | shared-runtime
	$(PYTHON) runtime_headers.py --profile $(1) \
	  --build-dir $(CUSTARD_HEADER_BUILD)/$(1) --output $(RUNTIME_DIR)/$(1)/EverParse.h \
	  --fstar "$(FSTAR_EXE)" --fstar-options "$(FSTAR_OPTIONS) $(OTHERFLAGS)" \
	  --jobs $(CUSTARD_HEADER_JOBS)
endef
$(foreach profile,$(PROFILES),$(eval $(call profile_rule,$(profile))))

$(RUNTIME_DIR)/static/EverParse.h: $(RUNTIME_DIR)/static/EverParseStreamPrimitives.h
$(RUNTIME_DIR)/lowstar/static/EverParse.h: $(RUNTIME_DIR)/lowstar/static/EverParseStreamPrimitives.h

shared-runtime:
	$(MAKE) -C $(LIB_3D_HOME) verify FSTAR_EXE="$(FSTAR_EXE)" OTHERFLAGS="$(OTHERFLAGS)"

headers: $(HEADER_FILES) $(CUI_FILES) $(COMPANION_FILES)

check-headers: headers
	$(PYTHON) test_runtime_headers.py
	$(PYTHON) check_runtime_headers.py --headers $(RUNTIME_DIR) \
	  --build-dir $(CUSTARD_HEADER_BUILD)/consumers \
	  $(if $(filter 1,$(EVERPARSE_TEST_32BIT)),--32bit) \
	  $(if $(filter 1,$(SANITIZE)),--sanitize)

clean-headers:
	rm -f $(HEADER_FILES) $(CUI_FILES) $(COMPANION_FILES) $(RUNTIME_HEADER_SETTINGS) $(RUNTIME_HEADER_SETTINGS).tmp
	rm -rf $(foreach profile,$(PROFILES),$(RUNTIME_DIR)/$(profile)/src $(RUNTIME_DIR)/$(profile)/checked)

FORCE:

.PHONY: all headers check-headers clean-headers shared-runtime FORCE
