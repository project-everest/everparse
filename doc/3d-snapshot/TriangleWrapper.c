#include "TriangleWrapper.h"
#include "EverParse.h"
#include "Triangle.h"
void TriangleEverParseError(char *x, char *y, char *z);
static char* TriangleStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_point";
		case 2: return "_point"; 
		default: return "";
	}
}

static char* TriangleFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y"; 
		default: return "";
	}
}

BOOLEAN TriangleCheckTriangle(uint8_t *base, uint32_t len) {
	InputBuffer s;
	s.base = base;
	s.len = len;
	uint64_t result = TriangleValidateTriangle(s, 0);
	if (EverParseResultIsError(result)) {
		TriangleEverParseError(
	TriangleStructNameOfErr(result),
			TriangleFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
