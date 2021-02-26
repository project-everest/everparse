#include "OrderedPairWrapper.h"
#include "EverParse.h"
#include "OrderedPair.h"
void OrderedPairEverParseError(char *x, char *y, char *z);
static char* OrderedPairStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point";
		case 6: return "OrderedPair._orderedPair";
		case 7: return "OrderedPair._orderedPair"; 
		default: return "";
	}
}

static char* OrderedPairFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "x";
		case 5: return "y";
		case 6: return "lesser";
		case 7: return "greater"; 
		default: return "";
	}
}

BOOLEAN OrderedPairCheckOrderedPair(uint8_t *base, uint32_t len) {
	uint64_t result = OrderedPairValidateOrderedPair(len, base, 0);
	if (EverParseResultIsError(result)) {
		OrderedPairEverParseError(
	OrderedPairStructNameOfErr(result),
			OrderedPairFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
