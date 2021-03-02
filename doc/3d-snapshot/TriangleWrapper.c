#include "TriangleWrapper.h"
#include "EverParse.h"
#include "Triangle.h"
void TriangleEverParseError(char *x, char *y, char *z);
static char* TriangleStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "Triangle2._point";
		case 2: return "Triangle2._point";
		case 3: return "Triangle2._triangle";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point"; 
		default: return "";
	}
}

static char* TriangleFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "corners";
		case 4: return "x";
		case 5: return "y"; 
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
