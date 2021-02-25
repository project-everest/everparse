#include "TaggedUnionWrapper.h"
#include "EverParse.h"
#include "TaggedUnion.h"
void TaggedUnionEverParseError(char *x, char *y, char *z);
static char* TaggedUnionStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point";
		case 6: return "OrderedPair._orderedPair";
		case 7: return "OrderedPair._orderedPair";
		case 8: return "HelloWorld._point";
		case 9: return "HelloWorld._point";
		case 10: return "ColoredPoint._point";
		case 11: return "ColoredPoint._point";
		case 12: return "ColoredPoint._coloredPoint1";
		case 13: return "ColoredPoint._coloredPoint2";
		case 14: return "Triangle2._point";
		case 15: return "Triangle2._point";
		case 16: return "Triangle2._triangle";
		case 17: return "Color._coloredPoint";
		case 18: return "Color._coloredPoint";
		case 19: return "Color._coloredPoint";
		case 20: return "ReadPair._Pair";
		case 21: return "ReadPair._Pair";
		case 22: return "GetFieldPtr._T";
		case 23: return "GetFieldPtr._T";
		case 24: return "BoundedSumConst._boundedSum";
		case 25: return "BoundedSumConst._boundedSum";
		case 26: return "TaggedUnion._int_payload";
		case 27: return "TaggedUnion._int_payload";
		case 28: return "TaggedUnion._int_payload";
		case 29: return "TaggedUnion._integer"; 
		default: return "";
	}
}

static char* TaggedUnionFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "x";
		case 5: return "y";
		case 6: return "lesser";
		case 7: return "greater";
		case 8: return "x";
		case 9: return "y";
		case 10: return "x";
		case 11: return "y";
		case 12: return "color";
		case 13: return "color";
		case 14: return "x";
		case 15: return "y";
		case 16: return "corners";
		case 17: return "col";
		case 18: return "x";
		case 19: return "y";
		case 20: return "first";
		case 21: return "second";
		case 22: return "f1";
		case 23: return "f2";
		case 24: return "left";
		case 25: return "right";
		case 26: return "value8";
		case 27: return "value16";
		case 28: return "value32";
		case 29: return "size"; 
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
