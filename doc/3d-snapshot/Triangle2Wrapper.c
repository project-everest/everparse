#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
void Triangle2EverParseError(char *StructName, char *FieldName, char *Reason);
static char* Triangle2StructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BF._BF";
		case 2: return "BF._BF";
		case 3: return "BF._BF";
		case 4: return "BF._BF2";
		case 5: return "BF._BF2";
		case 6: return "BF._BF2";
		case 7: return "Base._Pair";
		case 8: return "Base._Pair";
		case 9: return "Base._Mine";
		case 10: return "Base._Mine";
		case 11: return "BoundedSum._boundedSum";
		case 12: return "BoundedSum._boundedSum";
		case 13: return "BoundedSum.mySum";
		case 14: return "BoundedSumConst._boundedSum";
		case 15: return "BoundedSumConst._boundedSum";
		case 16: return "BoundedSumWhere._boundedSum";
		case 17: return "BoundedSumWhere._boundedSum";
		case 18: return "BoundedSumWhere._boundedSum";
		case 19: return "Color._coloredPoint";
		case 20: return "Color._coloredPoint";
		case 21: return "Color._coloredPoint";
		case 22: return "ColoredPoint._point";
		case 23: return "ColoredPoint._point";
		case 24: return "ColoredPoint._coloredPoint1";
		case 25: return "ColoredPoint._coloredPoint2";
		case 26: return "Derived._Triple";
		case 27: return "EnumConstraint._enum_constraint";
		case 28: return "EnumConstraint._enum_constraint";
		case 29: return "GetFieldPtr._T";
		case 30: return "GetFieldPtr._T";
		case 31: return "HelloWorld._point";
		case 32: return "HelloWorld._point";
		case 33: return "OrderedPair._orderedPair";
		case 34: return "OrderedPair._orderedPair";
		case 35: return "ReadPair._Pair";
		case 36: return "ReadPair._Pair";
		case 37: return "Smoker._smoker";
		case 38: return "Smoker._smoker";
		case 39: return "TaggedUnion._int_payload";
		case 40: return "TaggedUnion._int_payload";
		case 41: return "TaggedUnion._int_payload";
		case 42: return "TaggedUnion._integer";
		case 43: return "Triangle._point";
		case 44: return "Triangle._point";
		case 45: return "Triangle2._point";
		case 46: return "Triangle2._point";
		case 47: return "Triangle2._triangle"; 
		default: return "";
	}
}

static char* Triangle2FieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "z";
		case 4: return "x";
		case 5: return "y";
		case 6: return "z";
		case 7: return "first";
		case 8: return "second";
		case 9: return "f";
		case 10: return "g";
		case 11: return "left";
		case 12: return "right";
		case 13: return "bound";
		case 14: return "left";
		case 15: return "right";
		case 16: return "__precondition";
		case 17: return "left";
		case 18: return "right";
		case 19: return "col";
		case 20: return "x";
		case 21: return "y";
		case 22: return "x";
		case 23: return "y";
		case 24: return "color";
		case 25: return "color";
		case 26: return "third";
		case 27: return "col";
		case 28: return "x";
		case 29: return "f1";
		case 30: return "f2";
		case 31: return "x";
		case 32: return "y";
		case 33: return "lesser";
		case 34: return "greater";
		case 35: return "first";
		case 36: return "second";
		case 37: return "age";
		case 38: return "cigarettesConsumed";
		case 39: return "value8";
		case 40: return "value16";
		case 41: return "value32";
		case 42: return "size";
		case 43: return "x";
		case 44: return "y";
		case 45: return "x";
		case 46: return "y";
		case 47: return "corners"; 
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
