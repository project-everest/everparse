#include "TaggedUnionWrapper.h"
#include "EverParse.h"
#include "TaggedUnion.h"
void TaggedUnionEverParseError(char *x, char *y, char *z);
static char* TaggedUnionStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_int_payload";
		case 2: return "_int_payload";
		case 3: return "_int_payload";
		case 4: return "_integer"; 
		default: return "";
	}
}

static char* TaggedUnionFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "value8";
		case 2: return "value16";
		case 3: return "value32";
		case 4: return "size"; 
		default: return "";
	}
}

BOOLEAN TaggedUnionCheckInteger(uint8_t *base, uint32_t len) {
	uint64_t result = TaggedUnionValidateInteger(len, base, 0);
	if (EverParseResultIsError(result)) {
		TaggedUnionEverParseError(
	TaggedUnionStructNameOfErr(result),
			TaggedUnionFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
