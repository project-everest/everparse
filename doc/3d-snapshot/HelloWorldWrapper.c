#include "HelloWorldWrapper.h"
#include "EverParse.h"
#include "HelloWorld.h"
void HelloWorldEverParseError(char *x, char *y, char *z);
static char* HelloWorldStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "_point";
		case 2: return "_point"; 
		default: return "";
	}
}

static char* HelloWorldFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y"; 
		default: return "";
	}
}

BOOLEAN HelloWorldCheckPoint(uint8_t *base, uint32_t len) {
	uint64_t result = HelloWorldValidatePoint(len, base, 0);
	if (EverParseResultIsError(result)) {
		HelloWorldEverParseError(
	HelloWorldStructNameOfErr(result),
			HelloWorldFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
