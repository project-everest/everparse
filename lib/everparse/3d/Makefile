all: verify

EVERPARSE_SRC_PATH := $(realpath ../../..)/src

include $(EVERPARSE_SRC_PATH)/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse/pulse

# common.Makefile assembles `clean` from clean_rules, so extend it before the
# include. The KaRaMeL extraction of this prelude lives in the krml/
# subdirectory and has its own artifacts, which none of the shared rules reach.
clean_rules += clean-krml-extracted

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

clean-krml-extracted:
	+$(MAKE) -C krml clean

.PHONY: clean-krml-extracted
