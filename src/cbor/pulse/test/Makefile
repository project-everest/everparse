all: CBORTest

EVERCBOR_SRC_PATH = $(realpath ../../..)
EVERCBOR_LIB_PATH = $(realpath $(EVERCBOR_SRC_PATH)/..)/lib/evercbor
include $(EVERCBOR_SRC_PATH)/karamel.Makefile

.PHONY: all

.PHONY: CBORTest

CBORTest: CBORTest.exe
	./CBORTest.exe

CBORTest.o: CBORTest.c
	$(CC) -Werror -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I ../_output/ -c -o $@ $<

CBORTest.exe: CBORTest.o $(EVERCBOR_LIB_PATH)/evercbor.a
	$(CC) -o CBORTest.exe $^
