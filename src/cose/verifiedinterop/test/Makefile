all: signtest verifytest test

.PHONY: all

EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
ifeq (,$(HACL_HOME))
  HACL_HOME := $(EVERPARSE_PATH)/opt/hacl-star
endif
export HACL_HOME

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

SANFLAGS = -fsanitize=address -fsanitize=undefined

OUTPUT_DIRECTORY=../_output

CFLAGS += -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I $(OUTPUT_DIRECTORY)

$(HACL_HOME)/dist/gcc-compatible/libevercrypt.a:
	$(MAKE) -C $(dir $@)

signtest: signtest.c common.c $(OUTPUT_DIRECTORY)/CommonPulse.c $(OUTPUT_DIRECTORY)/COSE_Format.c $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.c $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(SANFLAGS) $(CFLAGS) $+ $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a -I _output -o $@

verifytest: verifytest.c common.c $(OUTPUT_DIRECTORY)/CommonPulse.c $(OUTPUT_DIRECTORY)/COSE_Format.c $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.c $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(SANFLAGS) $(CFLAGS) $+ $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a -I _output -o $@

bench: bench.c common.c $(OUTPUT_DIRECTORY)/CommonPulse.c $(OUTPUT_DIRECTORY)/COSE_Format.c $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.c $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	clang -O3 $(CFLAGS) $+ $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a -I _output -o $@

../../interop/.venv:
	$(MAKE) -C $(dir $@) $(notdir $@)

.PHONY: test
test: signtest verifytest ../../interop/.venv
	../../interop/.venv/bin/python test.py
