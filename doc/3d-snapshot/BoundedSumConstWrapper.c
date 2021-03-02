#include "BoundedSumConstWrapper.h"
#include "EverParse.h"
#include "BoundedSumConst.h"
void BoundedSumConstEverParseError(char *x, char *y, char *z);
static char* BoundedSumConstStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "BoundedSumConst._boundedSum";
		case 5: return "BoundedSumConst._boundedSum"; 
		default: return "";
	}
}

static char* BoundedSumConstFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "left";
		case 5: return "right"; 
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
