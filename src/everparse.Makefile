ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

ALREADY_CACHED := LowParse,$(ALREADY_CACHED)

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse
