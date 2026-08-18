all: CBORDetTest

EVERPARSE_SRC_PATH = $(realpath ../../../../..)

CBOR_LIB_PATH = $(realpath ..)
CBOR_INCLUDE_PATH = $(realpath ..)

# -Wno-pointer-sign because of string to uint8_t* conversion
CFLAGS += -Werror -I $(CBOR_INCLUDE_PATH) -g -Wno-pointer-sign

.PHONY: all

.PHONY: CBORDetTest

CBORDetTest: CBORDetTest.exe
	./CBORDetTest.exe

OBJ_FILES=main.o

$(OBJ_FILES): %.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

CBORDetTest.exe: $(OBJ_FILES) $(CBOR_LIB_PATH)/CBORDet.o
	$(CC) -o CBORDetTest.exe $^

clean:
	rm -f CBORDetTest.exe *.o

.PHONY: clean
