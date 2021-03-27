#include "BoundedSumConstWrapper.h"
#include "EverParse.h"
#include "BoundedSumConst.h"
void BoundedSumConstEverParseError(char *StructName, char *FieldName, char *Reason);
static char* BoundedSumConstStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BF._BF";
		case 2: return "BF._BF";
		case 3: return "BF._BF";
		case 4: return "BF._BF2";
		case 5: return "BF._BF2";
		case 6: return "BF._BF2";
		case 7: return "Base._Pair";
		case 8: return "Base._Pair";
		case 9: return "Base._Mine";
		case 10: return "Base._Mine";
		case 11: return "BoundedSum._boundedSum";
		case 12: return "BoundedSum._boundedSum";
		case 13: return "BoundedSum.mySum";
		case 14: return "BoundedSumConst._boundedSum";
		case 15: return "BoundedSumConst._boundedSum"; 
		default: return "";
	}
}

static char* BoundedSumConstFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "z";
		case 4: return "x";
		case 5: return "y";
		case 6: return "z";
		case 7: return "first";
		case 8: return "second";
		case 9: return "f";
		case 10: return "g";
		case 11: return "left";
		case 12: return "right";
		case 13: return "bound";
		case 14: return "left";
		case 15: return "right"; 
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
