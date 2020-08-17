#include "EverParse.h"
#include "OrderedPair.h"
void OrderedPairEverParseError(char *x, char *y, char *z);
static char* OrderedPairStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_orderedPair";
		case 2: return "_orderedPair"; 
		default: return "";
	}
}

static char* OrderedPairFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "lesser";
		case 2: return "greater"; 
		default: return "";
	}
}

BOOLEAN OrderedPairCheckOrderedPair(uint8_t *base, uint32_t len) {
	InputBuffer s;
	s.base = base;
	s.len = len;
	uint64_t result = OrderedPairValidateOrderedPair(s, 0);
	if (EverParseResultIsError(result)) {
		OrderedPairEverParseError(
	OrderedPairStructNameOfErr(result),
			OrderedPairFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}


