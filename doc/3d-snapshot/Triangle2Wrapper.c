#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
void Triangle2EverParseError(char *x, char *y, char *z);
static char* Triangle2StructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "Triangle2._point";
		case 2: return "Triangle2._point";
		case 3: return "Triangle2._triangle"; 
		default: return "";
	}
}

static char* Triangle2FieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "corners"; 
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
