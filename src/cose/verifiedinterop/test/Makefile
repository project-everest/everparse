all: signtest verifytest test

.PHONY: all

EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
ifeq (,$(HACL_HOME))
  HACL_HOME := $(CURDIR)/hacl-star
endif
export HACL_HOME
ifeq (,$(KRML_HOME))
  KRML_HOME := $(EVERPARSE_PATH)/opt/karamel
endif
export KRML_HOME

SANFLAGS = -fsanitize=address -fsanitize=undefined

CFLAGS += -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I ../../c

$(HACL_HOME)/dist/gcc-compatible/libevercrypt.a: $(HACL_HOME) $(KRML_HOME)
	$(MAKE) -C $(dir $@)

$(CURDIR)/hacl-star:
	rm -rf $@.tmp
	git clone https://github.com/hacl-star/hacl-star $@.tmp
	mv $@.tmp $@

$(EVERPARSE_PATH)/opt/karamel:
	+$(MAKE) -C $(dir $@) $(notdir $@)

COSE_EVERCRYPT_O=../../c/COSE_EverCrypt.o
COSE_FORMAT_O=../../c/COSE_Format.o
CBORDET_O=$(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.c

signtest: signtest.c common.c $(COSE_EVERCRYPT_O) $(COSE_FORMAT_O) $(CBORDET_O) $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(SANFLAGS) $(CFLAGS) $^ -I _output -o $@

verifytest: verifytest.c common.c $(COSE_EVERCRYPT_O) $(COSE_FORMAT_O) $(CBORDET_O) $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(SANFLAGS) $(CFLAGS) $^ -I _output -o $@

bench: bench.c common.c $(COSE_EVERCRYPT_O) $(COSE_FORMAT_O) $(CBORDET_O) $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	clang -O3 $(CFLAGS) $^ -I _output -o $@

../../.venv:
	$(MAKE) -C $(dir $@) $(notdir $@)

.PHONY: test
test: signtest verifytest ../../.venv
	../../.venv/bin/python test.py
