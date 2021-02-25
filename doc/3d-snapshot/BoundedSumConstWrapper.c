#include "BoundedSumConstWrapper.h"
#include "EverParse.h"
#include "BoundedSumConst.h"
void BoundedSumConstEverParseError(char *x, char *y, char *z);
static char* BoundedSumConstStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "ColoredPoint._point";
		case 2: return "ColoredPoint._point";
		case 3: return "ColoredPoint._coloredPoint1";
		case 4: return "ColoredPoint._coloredPoint2";
		case 5: return "Triangle._point";
		case 6: return "Triangle._point";
		case 7: return "OrderedPair._orderedPair";
		case 8: return "OrderedPair._orderedPair";
		case 9: return "HelloWorld._point";
		case 10: return "HelloWorld._point";
		case 11: return "Triangle2._point";
		case 12: return "Triangle2._point";
		case 13: return "Triangle2._triangle";
		case 14: return "Color._coloredPoint";
		case 15: return "Color._coloredPoint";
		case 16: return "Color._coloredPoint";
		case 17: return "ReadPair._Pair";
		case 18: return "ReadPair._Pair";
		case 19: return "GetFieldPtr._T";
		case 20: return "GetFieldPtr._T";
		case 21: return "BoundedSum._boundedSum";
		case 22: return "BoundedSum._boundedSum";
		case 23: return "BoundedSum.mySum";
		case 24: return "BoundedSumConst._boundedSum";
		case 25: return "BoundedSumConst._boundedSum"; 
		default: return "";
	}
}

static char* BoundedSumConstFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "color";
		case 4: return "color";
		case 5: return "x";
		case 6: return "y";
		case 7: return "lesser";
		case 8: return "greater";
		case 9: return "x";
		case 10: return "y";
		case 11: return "x";
		case 12: return "y";
		case 13: return "corners";
		case 14: return "col";
		case 15: return "x";
		case 16: return "y";
		case 17: return "first";
		case 18: return "second";
		case 19: return "f1";
		case 20: return "f2";
		case 21: return "left";
		case 22: return "right";
		case 23: return "bound";
		case 24: return "left";
		case 25: return "right"; 
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
