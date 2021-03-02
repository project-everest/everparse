#include "GetFieldPtrWrapper.h"
#include "EverParse.h"
#include "GetFieldPtr.h"
void GetFieldPtrEverParseError(char *x, char *y, char *z);
static char* GetFieldPtrStructNameOfErr(uint64_t err) {
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
		case 12: return "ColoredPoint._point";
		case 13: return "ColoredPoint._point";
		case 14: return "ColoredPoint._coloredPoint1";
		case 15: return "ColoredPoint._coloredPoint2";
		case 16: return "GetFieldPtr._T";
		case 17: return "GetFieldPtr._T"; 
		default: return "";
	}
}

static char* GetFieldPtrFieldNameOfErr(uint64_t err) {
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
		case 12: return "x";
		case 13: return "y";
		case 14: return "color";
		case 15: return "color";
		case 16: return "f1";
		case 17: return "f2"; 
		default: return "";
	}
}

BOOLEAN GetFieldPtrCheckT(uint8_t** out, uint8_t *base, uint32_t len) {
	uint64_t result = GetFieldPtrValidateT(out, len, base, 0);
	if (EverParseResultIsError(result)) {
		GetFieldPtrEverParseError(
	GetFieldPtrStructNameOfErr(result),
			GetFieldPtrFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
