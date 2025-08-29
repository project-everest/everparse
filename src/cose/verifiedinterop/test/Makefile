all: signtest verifytest test run-bench

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

CC     := clang
CFLAGS += -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I ../../c -I _output

$(HACL_HOME)/dist/gcc-compatible/libevercrypt.a: $(HACL_HOME) $(KRML_HOME)
	$(MAKE) -C $(dir $@)

$(CURDIR)/hacl-star:
	rm -rf $@.tmp
	git clone https://github.com/hacl-star/hacl-star $@.tmp
	mv $@.tmp $@

$(EVERPARSE_PATH)/opt/karamel:
	+$(MAKE) -C $(dir $@) $(notdir $@)

HEADERDEPS = ../../c/COSE_Format.h ../../c/COSE_EverCrypt.h $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.h

COSE_Format.o: ../../c/COSE_Format.c $(HEADERDEPS)

COSE_EverCrypt.o: ../../c/COSE_EverCrypt.c $(HEADERDEPS)

CBOR_Det.o: $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.c $(HEADERDEPS)

%.o:
	$(CC) $(CFLAGS) -c $< -o $@

signtest: signtest.c common.c COSE_EverCrypt.o COSE_Format.o CBOR_Det.o $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(CFLAGS) $^ -o $@

verifytest: verifytest.c common.c COSE_EverCrypt.o COSE_Format.o CBOR_Det.o $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(CFLAGS) $^ -o $@

bench: bench.c common.c COSE_EverCrypt.o COSE_Format.o CBOR_Det.o $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(CFLAGS) $^ -o $@

run-bench: bench test
	./$<

.PHONY: run-bench

../../.venv:
	$(MAKE) -C $(dir $@) $(notdir $@)

.PHONY: test
test: signtest verifytest ../../.venv
	../../.venv/bin/python test.py

clean:
	rm -f *.o signtest verifytest bench message.*
	rm -rf hacl-star

.PHONY: clean
