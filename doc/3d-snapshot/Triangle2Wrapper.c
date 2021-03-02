#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
void Triangle2EverParseError(char *x, char *y, char *z);
static char* Triangle2StructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "BoundedSumConst._boundedSum";
		case 5: return "BoundedSumConst._boundedSum";
		case 6: return "BoundedSumWhere._boundedSum";
		case 7: return "BoundedSumWhere._boundedSum";
		case 8: return "BoundedSumWhere._boundedSum";
		case 9: return "Color._coloredPoint";
		case 10: return "Color._coloredPoint";
		case 11: return "Color._coloredPoint";
		case 12: return "ColoredPoint._point";
		case 13: return "ColoredPoint._point";
		case 14: return "ColoredPoint._coloredPoint1";
		case 15: return "ColoredPoint._coloredPoint2";
		case 16: return "GetFieldPtr._T";
		case 17: return "GetFieldPtr._T";
		case 18: return "HelloWorld._point";
		case 19: return "HelloWorld._point";
		case 20: return "OrderedPair._orderedPair";
		case 21: return "OrderedPair._orderedPair";
		case 22: return "ReadPair._Pair";
		case 23: return "ReadPair._Pair";
		case 24: return "Smoker._smoker";
		case 25: return "Smoker._smoker";
		case 26: return "TaggedUnion._int_payload";
		case 27: return "TaggedUnion._int_payload";
		case 28: return "TaggedUnion._int_payload";
		case 29: return "TaggedUnion._integer";
		case 30: return "Triangle._point";
		case 31: return "Triangle._point";
		case 32: return "Triangle2._point";
		case 33: return "Triangle2._point";
		case 34: return "Triangle2._triangle"; 
		default: return "";
	}
}

static char* Triangle2FieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "left";
		case 5: return "right";
		case 6: return "__precondition";
		case 7: return "left";
		case 8: return "right";
		case 9: return "col";
		case 10: return "x";
		case 11: return "y";
		case 12: return "x";
		case 13: return "y";
		case 14: return "color";
		case 15: return "color";
		case 16: return "f1";
		case 17: return "f2";
		case 18: return "x";
		case 19: return "y";
		case 20: return "lesser";
		case 21: return "greater";
		case 22: return "first";
		case 23: return "second";
		case 24: return "age";
		case 25: return "cigarettesConsumed";
		case 26: return "value8";
		case 27: return "value16";
		case 28: return "value32";
		case 29: return "size";
		case 30: return "x";
		case 31: return "y";
		case 32: return "x";
		case 33: return "y";
		case 34: return "corners"; 
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
