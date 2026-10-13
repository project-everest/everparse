all: CBORNondetTest

EVERPARSE_HOME = $(realpath ../../../../../..)

CBOR_LIB_PATH = $(EVERPARSE_HOME)/lib/everparse
CBOR_INCLUDE_PATH = $(EVERPARSE_HOME)/include/everparse

CFLAGS += -Werror -I $(CBOR_INCLUDE_PATH)

.PHONY: all

.PHONY: CBORNondetTest

CBORNondetTest: CBORNondetTest.exe
	./CBORNondetTest.exe

OBJ_FILES=CBORNondetTest.o main.o qcbortests.o

$(OBJ_FILES): %.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

CBORNondetTest.exe: $(OBJ_FILES) $(CBOR_LIB_PATH)/CBORNondet.o
	$(CC) -o CBORNondetTest.exe $^

clean:
	rm -f CBORNondetTest.exe *.o

.PHONY: clean
