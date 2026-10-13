all: verify

EVERPARSE_HOME = $(realpath ../../../../..)
INCLUDE_PATHS += \
$(EVERPARSE_HOME)/src/cddl/spec \
$(EVERPARSE_HOME)/lib/everparse/cbor/spec \
$(EVERPARSE_HOME)/lib/everparse/cbor/pulse \
$(EVERPARSE_HOME)/src/cddl/pulse

ALREADY_CACHED := *,-CDDL.Spec,

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile
