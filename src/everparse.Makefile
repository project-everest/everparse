ifeq (,$(EVERPARSE_HOME))
  $(error "EVERPARSE_HOME must be set to the absolute path of the root of the EverParse repository or installation")
endif

include $(EVERPARSE_HOME)/src/karamel.Makefile

ALREADY_CACHED := LowParse,$(ALREADY_CACHED)

INCLUDE_PATHS += $(EVERPARSE_HOME)/src/lowparse
