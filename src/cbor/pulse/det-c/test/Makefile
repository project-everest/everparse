all: CBORDetTest

EVERCBOR_SRC_PATH = $(realpath ../../../..)

#EVERCBOR_LIB_PATH = $(realpath $(EVERCBOR_SRC_PATH)/..)/lib/evercbor
#EVERCBOR_INCLUDE_PATH = $(realpath $(EVERCBOR_SRC_PATH)/..)/include/evercbor
EVERCBOR_LIB_PATH = $(realpath ../extracted)
EVERCBOR_INCLUDE_PATH = $(realpath ../extracted)

include $(EVERCBOR_SRC_PATH)/karamel.Makefile

.PHONY: all

.PHONY: CBORDetTest

CBORDetTest: CBORDetTest.exe
	./CBORDetTest.exe

CBORDetTest.o: CBORDetTest.c
	$(CC) -Werror -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I $(EVERCBOR_INCLUDE_PATH) -c -o $@ $<

# CBORDetTest.c: gen/GenCBORDetTest.ml
# 	./gen/CBORDetTest.sh

#CBORDetTest.exe: CBORDetTest.o $(EVERCBOR_LIB_PATH)/evercbor.a
CBORDetTest.exe: CBORDetTest.o $(EVERCBOR_LIB_PATH)/CBORDet.o
	$(CC) -o CBORDetTest.exe $^
