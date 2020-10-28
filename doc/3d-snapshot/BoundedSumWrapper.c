#include "BoundedSumWrapper.h"
#include "EverParse.h"
#include "BoundedSum.h"
void BoundedSumEverParseError(char *x, char *y, char *z);
static char* BoundedSumStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_boundedSum";
		case 2: return "_boundedSum";
		case 3: return "mySum"; 
		default: return "";
	}
}

static char* BoundedSumFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound"; 
		default: return "";
	}
}

BOOLEAN BoundedSumCheckBoundedSum(uint32_t bound, uint8_t *base, uint32_t len) {
	InputBuffer s;
	s.base = base;
	s.len = len;
	uint64_t result = BoundedSumValidateBoundedSum(bound, s, 0);
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
	InputBuffer s;
	s.base = base;
	s.len = len;
	uint64_t result = BoundedSumValidateMySum(s, 0);
	if (EverParseResultIsError(result)) {
		BoundedSumEverParseError(
	BoundedSumStructNameOfErr(result),
			BoundedSumFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
