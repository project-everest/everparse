all: verify

EVERPARSE_SRC_PATH = $(realpath ..)

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse/pulse
ALREADY_CACHED := *,-Parquet,

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile

include $(EVERPARSE_SRC_PATH)/common.Makefile
