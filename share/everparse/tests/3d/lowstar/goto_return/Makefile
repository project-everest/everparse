# Test for --goto_for_early_return wrapper generation
# Generates wrappers and diffs against expected snapshot

EVERPARSE_HOME ?= $(realpath ../../../../../..)
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_API ?= lowstar
export EVERPARSE_API
EVERPARSE_EXE = $(EVERPARSE_HOME)/bin/everparse-3d.exe --api $(EVERPARSE_API) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(KRML_EXE),--karamel "$(KRML_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")
OUTPUT_DIR = output

all: test

$(OUTPUT_DIR):
	mkdir -p $@

$(OUTPUT_DIR)/GotoReturnWrapper.c $(OUTPUT_DIR)/GotoReturnWrapper.h: GotoReturn.3d | $(OUTPUT_DIR)
	$(EVERPARSE_EXE) --odir $(OUTPUT_DIR) --goto_for_early_return --complete_wrappers GotoReturn.3d

test: $(OUTPUT_DIR)/GotoReturnWrapper.c $(OUTPUT_DIR)/GotoReturnWrapper.h
	diff -u snapshot/GotoReturnWrapper.c $(OUTPUT_DIR)/GotoReturnWrapper.c
	diff -u snapshot/GotoReturnWrapper.h $(OUTPUT_DIR)/GotoReturnWrapper.h
	@echo "PASS: goto_for_early_return snapshot test"

update-snapshot: $(OUTPUT_DIR)/GotoReturnWrapper.c $(OUTPUT_DIR)/GotoReturnWrapper.h
	cp $(OUTPUT_DIR)/GotoReturnWrapper.c snapshot/
	cp $(OUTPUT_DIR)/GotoReturnWrapper.h snapshot/

clean:
	rm -rf $(OUTPUT_DIR)

.PHONY: all test update-snapshot clean
