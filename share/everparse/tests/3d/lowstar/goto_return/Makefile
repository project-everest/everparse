# Keep the unsupported formatting option an explicit error.

EVERPARSE_HOME ?= $(realpath ../../../../../..)
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_API ?= lowstar
export EVERPARSE_API
EVERPARSE_EXE = $(EVERPARSE_HOME)/bin/everparse-3d.exe --api $(EVERPARSE_API) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(KRML_EXE),--karamel "$(KRML_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")
OUTPUT_DIR = output

all: test

$(OUTPUT_DIR):
	mkdir -p $@

test: | $(OUTPUT_DIR)
	! $(EVERPARSE_EXE) --odir $(OUTPUT_DIR) --goto_for_early_return --complete_wrappers GotoReturn.3d > $(OUTPUT_DIR)/diagnostic.log 2>&1
	grep -F -- '--goto_for_early_return: not implemented yet' $(OUTPUT_DIR)/diagnostic.log

clean:
	rm -rf $(OUTPUT_DIR)

.PHONY: all test clean
