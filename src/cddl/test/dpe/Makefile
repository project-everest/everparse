all: verify

EVERPARSE_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += \
$(EVERPARSE_SRC_PATH)/cddl/spec \
$(EVERPARSE_SRC_PATH)/cbor/spec \
$(EVERPARSE_SRC_PATH)/cbor/pulse \
$(KRML_HOME)/krmllib \
$(KRML_HOME)/krmllib/obj \
$(PULSE_HOME)/lib/pulse \
$(EVERPARSE_SRC_PATH)/cddl/pulse \
$(EVERPARSE_SRC_PATH)/cddl/tool \
$(EVERPARSE_SRC_PATH)/../lib/evercddl/lib \
$(EVERPARSE_SRC_PATH)/../lib/evercddl/plugin \
../util \
../_output \
$(PULSE_HOME)/../share/pulse/examples/dice \
$(PULSE_HOME)/../share/pulse/examples/dice/_cache


ALREADY_CACHED := *,-CDDL.Spec,

include $(EVERPARSE_SRC_PATH)/common.Makefile