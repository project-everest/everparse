include include.Makefile

EVERPARSE_INPUT_DIR := .
EVERPARSE_OUTPUT_DIR := tmp
EVERPARSE_CMD := $(3D)

all: world

.PHONY: all world

include $(EVERPARSE_OUTPUT_DIR)/EverParse.Makefile

world: $(EVERPARSE_ALL_C_FILES)
