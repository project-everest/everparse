#include "BoundedSumWrapper.h"
#include "EverParse.h"
#include "BoundedSum.h"
void BoundedSumEverParseError(char *x, char *y, char *z);
static char* BoundedSumStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "Base._Pair";
		case 2: return "Base._Pair";
		case 3: return "Base._Mine";
		case 4: return "Base._Mine";
		case 5: return "BoundedSum._boundedSum";
		case 6: return "BoundedSum._boundedSum";
		case 7: return "BoundedSum.mySum"; 
		default: return "";
	}
}

static char* BoundedSumFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "first";
		case 2: return "second";
		case 3: return "f";
		case 4: return "g";
		case 5: return "left";
		case 6: return "right";
		case 7: return "bound"; 
		default: return "";
	}
}

BOOLEAN BoundedSumCheckBoundedSum(uint32_t bound, uint8_t *base, uint32_t len) {
	uint64_t result = BoundedSumValidateBoundedSum(bound, len, base, 0);
	if (EverParseResultIsError(result)) {
		BoundedSumEverParseError(
	BoundedSumStructNameOfErr(result),
			BoundedSumFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}

BOOLEAN BoundedSumCheckMySum(uint8_t *base, uint32_t len) {
	uint64_t result = BoundedSumValidateMySum(len, base, 0);
	if (EverParseResultIsError(result)) {
		BoundedSumEverParseError(
	BoundedSumStructNameOfErr(result),
			BoundedSumFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
