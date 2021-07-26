#include "ColorWrapper.h"
#include "EverParse.h"
#include "Color.h"
void ColorEverParseError(char *StructName, char *FieldName, char *Reason);
static char* ColorStructNameOfErr(uint64_t err) {
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
		case 16: return "BoundedSumWhere._boundedSum";
		case 17: return "BoundedSumWhere._boundedSum";
		case 18: return "BoundedSumWhere._boundedSum";
		case 19: return "Color._coloredPoint";
		case 20: return "Color._coloredPoint";
		case 21: return "Color._coloredPoint"; 
		default: return "";
	}
}

static char* ColorFieldNameOfErr(uint64_t err) {
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
		case 16: return "__precondition";
		case 17: return "left";
		case 18: return "right";
		case 19: return "col";
		case 20: return "x";
		case 21: return "y"; 
		default: return "";
	}
}

BOOLEAN ColorCheckColoredPoint(uint8_t *base, uint32_t len) {
	uint64_t result = ColorValidateColoredPoint(len, base, 0);
	if (EverParseResultIsError(result)) {
		ColorEverParseError(
	ColorStructNameOfErr(result),
			ColorFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
