#include "BoundedSumConstWrapper.h"
#include "EverParse.h"
#include "BoundedSumConst.h"
void BoundedSumConstEverParseError(char *x, char *y, char *z);
static char* BoundedSumConstStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "Base._Pair";
		case 2: return "Base._Pair";
		case 3: return "Base._Mine";
		case 4: return "Base._Mine";
		case 5: return "BoundedSum._boundedSum";
		case 6: return "BoundedSum._boundedSum";
		case 7: return "BoundedSum.mySum";
		case 8: return "BoundedSumConst._boundedSum";
		case 9: return "BoundedSumConst._boundedSum"; 
		default: return "";
	}
}

static char* BoundedSumConstFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "first";
		case 2: return "second";
		case 3: return "f";
		case 4: return "g";
		case 5: return "left";
		case 6: return "right";
		case 7: return "bound";
		case 8: return "left";
		case 9: return "right"; 
		default: return "";
	}
}

BOOLEAN BoundedSumConstCheckBoundedSum(uint8_t *base, uint32_t len) {
	uint64_t result = BoundedSumConstValidateBoundedSum(len, base, 0);
	if (EverParseResultIsError(result)) {
		BoundedSumConstEverParseError(
	BoundedSumConstStructNameOfErr(result),
			BoundedSumConstFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
