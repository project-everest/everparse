all: CBORDetTest

EVERPARSE_SRC_PATH = $(realpath ../../../..)

#EVERPARSE_LIB_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)/lib/evercbor
#EVERPARSE_INCLUDE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)/include/evercbor
EVERPARSE_LIB_PATH = $(realpath ../extracted)
EVERPARSE_INCLUDE_PATH = $(realpath ../extracted)

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

.PHONY: all

.PHONY: CBORDetTest

CBORDetTest: CBORDetTest.exe
	./CBORDetTest.exe

CBORDetTest.o: CBORDetTest.c
	$(CC) -Werror -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I $(EVERPARSE_INCLUDE_PATH) -c -o $@ $<

# CBORDetTest.c: gen/GenCBORDetTest.ml
# 	./gen/CBORDetTest.sh

#CBORDetTest.exe: CBORDetTest.o $(EVERPARSE_LIB_PATH)/evercbor.a
CBORDetTest.exe: CBORDetTest.o $(EVERPARSE_LIB_PATH)/CBORDet.o
	$(CC) -o CBORDetTest.exe $^
