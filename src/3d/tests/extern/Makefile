all: EverParseStream.o

%.o:
	$(CC) -I ../../prelude/extern -I ../.. -o $@ -c -Wall --pedantic $<

clean:
	rm -f *.o *~

EverParseStream.o: EverParseStream.c EverParseStream.h

.PHONY: all clean
