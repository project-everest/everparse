#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
void Triangle2EverParseError(char *x, char *y, char *z);
static char* Triangle2StructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point";
		case 6: return "OrderedPair._orderedPair";
		case 7: return "OrderedPair._orderedPair";
		case 8: return "HelloWorld._point";
		case 9: return "HelloWorld._point";
		case 10: return "ColoredPoint._point";
		case 11: return "ColoredPoint._point";
		case 12: return "ColoredPoint._coloredPoint1";
		case 13: return "ColoredPoint._coloredPoint2";
		case 14: return "Triangle2._point";
		case 15: return "Triangle2._point";
		case 16: return "Triangle2._triangle"; 
		default: return "";
	}
}

static char* Triangle2FieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "x";
		case 5: return "y";
		case 6: return "lesser";
		case 7: return "greater";
		case 8: return "x";
		case 9: return "y";
		case 10: return "x";
		case 11: return "y";
		case 12: return "color";
		case 13: return "color";
		case 14: return "x";
		case 15: return "y";
		case 16: return "corners"; 
		default: return "";
	}
}

BOOLEAN Triangle2CheckTriangle(uint8_t *base, uint32_t len) {
	uint64_t result = Triangle2ValidateTriangle(len, base, 0);
	if (EverParseResultIsError(result)) {
		Triangle2EverParseError(
	Triangle2StructNameOfErr(result),
			Triangle2FieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
