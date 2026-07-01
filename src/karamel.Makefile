ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif
include $(EVERPARSE_SRC_PATH)/windows.Makefile

ALREADY_CACHED := C,LowStar,$(ALREADY_CACHED)

# Do not run `krml -locate` during the Makefile parsing. Only when the command runs.
ifeq (,$(KRML_LIB))
  KRML_LIB := "$$("$(KRML_EXE)" -locate-krmllib)"
endif
INCLUDE_PATHS += $ $(KRML_LIB) $(KRML_LIB)/obj

ifeq (,$(KRML_INCLUDE))
  KRML_INCLUDE := "$$("$(KRML_EXE)" -locate-include)"
endif
CFLAGS += -I $(KRML_INCLUDE) -I $(KRML_LIB)/dist/generic
