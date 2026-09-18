EVERPARSE_SRC_PATH = $(realpath ../..)

.PHONY: all
all: test run-bench

.PHONY: test
test: signtest.exe verifytest.exe ../.venv
	../.venv/bin/python test.py

.PHONY: run-bench
run-bench: bench.exe
	./$<

../.venv:
	$(MAKE) -C $(dir $@) $(notdir $@)

# SANFLAGS += -fsanitize=address -fsanitize=undefined
# CFLAGS += $(SANFLAGS)
# LDFLAGS += $(SANFLAGS)
CC     := clang
LDFLAGS += -lssl -lcrypto
CFLAGS += -O3
CFLAGS += -I ../c -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c
CFLAGS += -Wall -Wenum-conversion
# Custard emits the whole program as one translation unit, so COSE_Format.o
# also contains the EverCrypt-backed entry points this suite does not use.
# Section GC drops them, and with them the need to link libevercrypt.
CFLAGS += -ffunction-sections -fdata-sections
LDFLAGS += -Wl,--gc-sections

HEADERDEPS = ../c/COSE_Format.h ../c/COSE_OpenSSL.h $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.h

common.o: common.c $(HEADERDEPS)
signtest.o: signtest.c $(HEADERDEPS) common.h
verifytest.o: verifytest.c $(HEADERDEPS) common.h
bench.o: bench.c $(HEADERDEPS) common.h

%.o:
	$(CC) $(CFLAGS) -c $< -o $@

COSE_Format.o: ../c/COSE_Format.c $(HEADERDEPS)

COSE_OpenSSL.o: ../c/COSE_OpenSSL.c $(HEADERDEPS)

%.exe:
	$(CC) $(LDFLAGS) $+ -o $@

signtest.exe: signtest.o common.o COSE_OpenSSL.o COSE_Format.o
verifytest.exe: verifytest.o common.o COSE_OpenSSL.o COSE_Format.o
bench.exe: bench.o common.o COSE_OpenSSL.o COSE_Format.o

clean:
	rm -f *.o signtest.exe verifytest.exe bench.exe message.*

.PHONY: clean
