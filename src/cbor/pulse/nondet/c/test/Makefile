all: CBORNondetTest

EVERPARSE_SRC_PATH = $(realpath ../../../../..)

#EVERPARSE_LIB_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)/lib/evercbor
#EVERPARSE_INCLUDE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)/include/evercbor
EVERPARSE_LIB_PATH = $(realpath ..)
EVERPARSE_INCLUDE_PATH = $(realpath ..)

CFLAGS += -Werror -I $(EVERPARSE_INCLUDE_PATH)

.PHONY: all

.PHONY: CBORNondetTest

CBORNondetTest: CBORNondetTest.exe
	./CBORNondetTest.exe

OBJ_FILES=CBORNondetTest.o main.o

$(OBJ_FILES): %.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

# CBORNondetTest.c: gen/GenCBORNondetTest.ml
# 	./gen/CBORNondetTest.sh

#CBORNondetTest.exe: CBORNondetTest.o $(EVERPARSE_LIB_PATH)/evercbor.a
CBORNondetTest.exe: $(OBJ_FILES) $(EVERPARSE_LIB_PATH)/CBORNondet.o
	$(CC) -o CBORNondetTest.exe $^

clean:
	rm -f CBORNondetTest.exe *.o

.PHONY: clean
