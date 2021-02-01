#include "GetFieldPtrWrapper.h"
#include "EverParse.h"
#include "GetFieldPtr.h"
void GetFieldPtrEverParseError(char *x, char *y, char *z);
static char* GetFieldPtrStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "GetFieldPtr._T";
		case 2: return "GetFieldPtr._T"; 
		default: return "";
	}
}

static char* GetFieldPtrFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "f1";
		case 2: return "f2"; 
		default: return "";
	}
}

BOOLEAN GetFieldPtrCheckT(uint8_t** out, uint8_t *base, uint32_t len) {
	uint64_t result = GetFieldPtrValidateT(out, len, base, 0);
	if (EverParseResultIsError(result)) {
		GetFieldPtrEverParseError(
	GetFieldPtrStructNameOfErr(result),
			GetFieldPtrFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
