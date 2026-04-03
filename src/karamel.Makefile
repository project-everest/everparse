ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif
include $(EVERPARSE_SRC_PATH)/windows.Makefile

ALREADY_CACHED := C,LowStar,$(ALREADY_CACHED)

INCLUDE_PATHS += $(KRML_HOME)/krmllib $(KRML_HOME)/krmllib/obj

CFLAGS += -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic
