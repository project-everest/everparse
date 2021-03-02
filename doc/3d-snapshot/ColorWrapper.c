#include "ColorWrapper.h"
#include "EverParse.h"
#include "Color.h"
void ColorEverParseError(char *x, char *y, char *z);
static char* ColorStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "BoundedSumConst._boundedSum";
		case 5: return "BoundedSumConst._boundedSum";
		case 6: return "BoundedSumWhere._boundedSum";
		case 7: return "BoundedSumWhere._boundedSum";
		case 8: return "BoundedSumWhere._boundedSum";
		case 9: return "Color._coloredPoint";
		case 10: return "Color._coloredPoint";
		case 11: return "Color._coloredPoint"; 
		default: return "";
	}
}

static char* ColorFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "left";
		case 5: return "right";
		case 6: return "__precondition";
		case 7: return "left";
		case 8: return "right";
		case 9: return "col";
		case 10: return "x";
		case 11: return "y"; 
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
