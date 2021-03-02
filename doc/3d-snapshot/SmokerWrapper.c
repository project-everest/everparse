#include "SmokerWrapper.h"
#include "EverParse.h"
#include "Smoker.h"
void SmokerEverParseError(char *x, char *y, char *z);
static char* SmokerStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "Triangle2._point";
		case 2: return "Triangle2._point";
		case 3: return "Triangle2._triangle";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point";
		case 6: return "TaggedUnion._int_payload";
		case 7: return "TaggedUnion._int_payload";
		case 8: return "TaggedUnion._int_payload";
		case 9: return "TaggedUnion._integer";
		case 10: return "Smoker._smoker";
		case 11: return "Smoker._smoker"; 
		default: return "";
	}
}

static char* SmokerFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "corners";
		case 4: return "x";
		case 5: return "y";
		case 6: return "value8";
		case 7: return "value16";
		case 8: return "value32";
		case 9: return "size";
		case 10: return "age";
		case 11: return "cigarettesConsumed"; 
		default: return "";
	}
}

BOOLEAN SmokerCheckSmoker(uint8_t *base, uint32_t len) {
	uint64_t result = SmokerValidateSmoker(len, base, 0);
	if (EverParseResultIsError(result)) {
		SmokerEverParseError(
	SmokerStructNameOfErr(result),
			SmokerFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
