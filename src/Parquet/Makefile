all: verify

EVERPARSE_SRC_PATH = $(realpath ..)

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile

ALREADY_CACHED := *,-Parquet,

include $(EVERPARSE_SRC_PATH)/common.Makefile
