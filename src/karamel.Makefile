ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif
include $(EVERPARSE_SRC_PATH)/windows.Makefile

ALREADY_CACHED := C,LowStar,$(ALREADY_CACHED)

# Do not run `krml -locate` during the Makefile parsing. Only when the command runs.
ifeq (,$(KRML_LIB))
  KRML_LIB := "$$("$(KRML_EXE)" -locate-krmllib)"
  ifeq ($(OS),Windows_NT)
    KRML_LIB := "$$(cygpath -m "$$(echo $(KRML_LIB) | sed 's!\r!!g')")"
  endif
endif

# Use `FSTAR_OPTIONS += --include` instead of `INCLUDE_PATHS` because some Makefiles include `fstar.Makefile` instead of `common.Makefile`, and also because `krml -locate` contains whitespace that `addprefix --include` will mishandle
FSTAR_OPTIONS += --include $(KRML_LIB) --include $(KRML_LIB)/obj

ifeq (,$(KRML_INCLUDE))
  KRML_INCLUDE := "$$("$(KRML_EXE)" -locate-include)"
endif
CFLAGS += -I $(KRML_INCLUDE) -I $(KRML_LIB)/dist/generic
