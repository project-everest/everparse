all: verify

EVERPARSE_HOME := $(realpath ../../..)

include $(EVERPARSE_HOME)/lib/everparse/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/lowparse

# common.Makefile assembles `clean` from clean_rules, so extend it before the
# include. The KaRaMeL extraction of this prelude lives in the krml/
# subdirectory and has its own artifacts, which none of the shared rules reach.
clean_rules += clean-krml-extracted

include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

clean-krml-extracted:
	+$(MAKE) -C krml clean

.PHONY: clean-krml-extracted
