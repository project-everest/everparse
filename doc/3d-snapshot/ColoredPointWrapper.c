#include "ColoredPointWrapper.h"
#include "EverParse.h"
#include "ColoredPoint.h"
void ColoredPointEverParseError(char *x, char *y, char *z);
static char* ColoredPointStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_point";
		case 2: return "_point";
		case 3: return "_coloredPoint1";
		case 4: return "_coloredPoint2"; 
		default: return "";
	}
}

static char* ColoredPointFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "color";
		case 4: return "color"; 
		default: return "";
	}
}

BOOLEAN ColoredPointCheckColoredPoint1(uint8_t *base, uint32_t len) {
	InputBuffer s;
	s.base = base;
	s.len = len;
	uint64_t result = ColoredPointValidateColoredPoint1(s, 0);
	if (EverParseResultIsError(result)) {
		ColoredPointEverParseError(
	ColoredPointStructNameOfErr(result),
			ColoredPointFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ColoredPointCheckColoredPoint2(uint8_t *base, uint32_t len) {
	InputBuffer s;
	s.base = base;
	s.len = len;
	uint64_t result = ColoredPointValidateColoredPoint2(s, 0);
	if (EverParseResultIsError(result)) {
		ColoredPointEverParseError(
	ColoredPointStructNameOfErr(result),
			ColoredPointFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
