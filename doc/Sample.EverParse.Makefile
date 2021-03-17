all: test

EVERPARSE_CMD=/path/to/everparse.sh
EVERPARSE_OUTPUT_DIR=obj
EVERPARSE_INPUT_DIR=src

everparse_makefile=$(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile
source_files=$(wildcard $(EVERPARSE_INPUT_DIR)/*.3d)

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

$(everparse_makefile): $(source_files) $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --makefile gmake --makefile_name $@ $(source_files)

include $(everparse_makefile)

test: $(EVERPARSE_ALL_O_FILES)

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all test clean
