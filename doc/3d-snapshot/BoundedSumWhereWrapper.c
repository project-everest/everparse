#include "BoundedSumWhereWrapper.h"
#include "EverParse.h"
#include "BoundedSumWhere.h"
void BoundedSumWhereEverParseError(char *x, char *y, char *z);
static char* BoundedSumWhereStructNameOfErr(uint64_t err) {
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
		case 12: return "ReadPair._Pair";
		case 13: return "ReadPair._Pair";
		case 14: return "OrderedPair._orderedPair";
		case 15: return "OrderedPair._orderedPair";
		case 16: return "HelloWorld._point";
		case 17: return "HelloWorld._point";
		case 18: return "GetFieldPtr._T";
		case 19: return "GetFieldPtr._T";
		case 20: return "Base._Pair";
		case 21: return "Base._Pair";
		case 22: return "Base._Mine";
		case 23: return "Base._Mine";
		case 24: return "Base._Dummy";
		case 25: return "Derived._Triple";
		case 26: return "ColoredPoint._point";
		case 27: return "ColoredPoint._point";
		case 28: return "ColoredPoint._coloredPoint1";
		case 29: return "ColoredPoint._coloredPoint2";
		case 30: return "Color._coloredPoint";
		case 31: return "Color._coloredPoint";
		case 32: return "Color._coloredPoint";
		case 33: return "BoundedSumWhere._boundedSum";
		case 34: return "BoundedSumWhere._boundedSum";
		case 35: return "BoundedSumWhere._boundedSum"; 
		default: return "";
	}
}

static char* BoundedSumWhereFieldNameOfErr(uint64_t err) {
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
		case 12: return "first";
		case 13: return "second";
		case 14: return "lesser";
		case 15: return "greater";
		case 16: return "x";
		case 17: return "y";
		case 18: return "f1";
		case 19: return "f2";
		case 20: return "first";
		case 21: return "second";
		case 22: return "f";
		case 23: return "g";
		case 24: return "dummy";
		case 25: return "third";
		case 26: return "x";
		case 27: return "y";
		case 28: return "color";
		case 29: return "color";
		case 30: return "col";
		case 31: return "x";
		case 32: return "y";
		case 33: return "__precondition";
		case 34: return "left";
		case 35: return "right"; 
		default: return "";
	}
}

BOOLEAN BoundedSumWhereCheckBoundedSum(uint32_t bound, uint8_t *base, uint32_t len) {
	uint64_t result = BoundedSumWhereValidateBoundedSum(bound, len, base, 0);
	if (EverParseResultIsError(result)) {
		BoundedSumWhereEverParseError(
	BoundedSumWhereStructNameOfErr(result),
			BoundedSumWhereFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
