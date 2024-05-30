all: CBORTest

EVERCBOR_SRC_PATH = $(realpath ../../..)
include $(EVERCBOR_SRC_PATH)/karamel.Makefile

.PHONY: all

.PHONY: CBORTest

CBORTest: CBORTest.exe
	./CBORTest.exe

CBORTest.o: CBORTest.c
	$(CC) -Werror -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I ../_output/ -c -o $@ $<

CBORTest.exe: CBORTest.o ../_output/CBOR_Pulse.o $(EVERCBOR_SRC_PATH)/cbor/steel/impl/out/CBOR.o
	$(CC) -o CBORTest.exe $^
