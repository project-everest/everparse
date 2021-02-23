#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
void Triangle2EverParseError(char *x, char *y, char *z);
static char* Triangle2StructNameOfErr(uint64_t err) {
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
		default: return "";
	}
}

static char* Triangle2FieldNameOfErr(uint64_t err) {
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
