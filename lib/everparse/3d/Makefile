all: verify

EVERPARSE_HOME := $(realpath ../../..)

include $(EVERPARSE_HOME)/lib/everparse/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/lowparse

# Native runtime header and CUI generation is driven, and cleaned, by
# src/3d/runtime.

include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
include $(EVERPARSE_HOME)/lib/everparse/common.Makefile
