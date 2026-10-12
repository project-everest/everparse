all: verify

EVERPARSE_HOME = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..)

include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/everparse.Makefile

ALREADY_CACHED := *,-LowParse.Pulse,
OUTPUT_DIRECTORY := _output

include $(EVERPARSE_HOME)/src/common.Makefile
