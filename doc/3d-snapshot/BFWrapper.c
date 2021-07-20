#include "BFWrapper.h"
#include "EverParse.h"
#include "BF.h"
void BFEverParseError(char *StructName, char *FieldName, char *Reason);
static char* BFStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BF._BF";
		case 2: return "BF._BF";
		case 3: return "BF._BF";
		case 4: return "BF._BF2";
		case 5: return "BF._BF2";
		case 6: return "BF._BF2"; 
		default: return "";
	}
}

static char* BFFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "x";
		case 2: return "y";
		case 3: return "z";
		case 4: return "x";
		case 5: return "y";
		case 6: return "z"; 
		default: return "";
	}
}

BOOLEAN BfCheckDummy(uint8_t *base, uint32_t len) {
	uint32_t position = 0;
	EverParseInputBuffer inputBuffer;
	inputBuffer.buf = base;
	inputBuffer.len = len;
	inputBuffer.pos = &position;
	{
		uint64_t result = BfValidateDummy(inputBuffer);
		if (EverParseResultIsError(result)) {
			BFEverParseError(
				BFStructNameOfErr(result),
				BFFieldNameOfErr (result),
				EverParseErrorReasonOfResult(result));
			return FALSE;
		}
	};
	return TRUE;
}
