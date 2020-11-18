#include "ReadPairWrapper.h"
#include "EverParse.h"
#include "ReadPair.h"
void ReadPairEverParseError(char *x, char *y, char *z);
static char* ReadPairStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_Pair";
		case 2: return "_Pair"; 
		default: return "";
	}
}

static char* ReadPairFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "first";
		case 2: return "second"; 
		default: return "";
	}
}

BOOLEAN ReadPairCheckPair(uint32_t* x, uint32_t* y, uint8_t *base, uint32_t len) {
	uint64_t result = ReadPairValidatePair(x, y, len, base, 0);
	if (EverParseResultIsError(result)) {
		ReadPairEverParseError(
	ReadPairStructNameOfErr(result),
			ReadPairFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
