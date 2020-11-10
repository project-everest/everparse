#include "SmokerWrapper.h"
#include "EverParse.h"
#include "Smoker.h"
void SmokerEverParseError(char *x, char *y, char *z);
static char* SmokerStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_smoker";
		case 2: return "_smoker"; 
		default: return "";
	}
}

static char* SmokerFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "age";
		case 2: return "cigarettesConsumed"; 
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
