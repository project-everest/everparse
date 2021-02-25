#include "TriangleWrapper.h"
#include "EverParse.h"
#include "Triangle.h"
void TriangleEverParseError(char *x, char *y, char *z);
static char* TriangleStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "ColoredPoint._point";
		case 2: return "ColoredPoint._point";
		case 3: return "ColoredPoint._coloredPoint1";
		case 4: return "ColoredPoint._coloredPoint2";
		case 5: return "Triangle._point";
		case 6: return "Triangle._point"; 
		default: return "";
	}
}

static char* TriangleFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "color";
		case 4: return "color";
		case 5: return "x";
		case 6: return "y"; 
		default: return "";
	}
}

BOOLEAN TriangleCheckTriangle(uint8_t *base, uint32_t len) {
	uint64_t result = TriangleValidateTriangle(len, base, 0);
	if (EverParseResultIsError(result)) {
		TriangleEverParseError(
	TriangleStructNameOfErr(result),
			TriangleFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
