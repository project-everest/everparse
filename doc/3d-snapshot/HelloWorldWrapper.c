#include "HelloWorldWrapper.h"
#include "EverParse.h"
#include "HelloWorld.h"
void HelloWorldEverParseError(char *x, char *y, char *z);
static char* HelloWorldStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "ColoredPoint._point";
		case 2: return "ColoredPoint._point";
		case 3: return "ColoredPoint._coloredPoint1";
		case 4: return "ColoredPoint._coloredPoint2";
		case 5: return "Triangle._point";
		case 6: return "Triangle._point";
		case 7: return "OrderedPair._orderedPair";
		case 8: return "OrderedPair._orderedPair";
		case 9: return "HelloWorld._point";
		case 10: return "HelloWorld._point"; 
		default: return "";
	}
}

static char* HelloWorldFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "color";
		case 4: return "color";
		case 5: return "x";
		case 6: return "y";
		case 7: return "lesser";
		case 8: return "greater";
		case 9: return "x";
		case 10: return "y"; 
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
