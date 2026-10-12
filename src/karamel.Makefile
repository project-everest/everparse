ifeq (,$(EVERPARSE_HOME))
  $(error "EVERPARSE_HOME must be set to the absolute path of the root of the EverParse repository or installation")
endif
include $(EVERPARSE_HOME)/src/windows.Makefile

ALREADY_CACHED := C,LowStar,$(ALREADY_CACHED)

# CFLAGS += -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic
