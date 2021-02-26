#include "TriangleWrapper.h"
#include "EverParse.h"
#include "Triangle.h"
void TriangleEverParseError(char *x, char *y, char *z);
static char* TriangleStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point"; 
		default: return "";
	}
}

static char* TriangleFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
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
