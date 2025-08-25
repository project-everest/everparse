all: verify extract

EVERPARSE_SRC_PATH = $(realpath ..)

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse/pulse $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse
ALREADY_CACHED := *,-Parquet,-CDDL.Pulse.Types.Base,-CDDL.Spec.Bijection,
FSTAR_DEP_OPTIONS += --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'
OUTPUT_DIRECTORY := _output

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: cpp/EverParquet.c

cpp/EverParquet.c: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -skip-compilation -bundle Parquet.Pulse.Toplevel+Parquet.Pulse.Toplevel0=\*[rename=EverParquet] -skip-makefiles -tmpdir $(dir $@) -header noheader.txt $(ALL_KRML_FILES)
