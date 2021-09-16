#include "DerivedWrapper.h"
#include "EverParse.h"
#include "Derived.h"
void DerivedEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename,
	const char *fieldname,
	const char *reason,
	uint8_t *context,
	EverParseInputBuffer input,
	uint64_t start_pos)
{
	EverParseErrorFrame *frame = (EverParseErrorFrame*)context;
	EverParseDefaultErrorHandler(
		typename,
		fieldname,
		reason,
		frame,
		input,
		start_pos
	);
}

BOOLEAN DerivedCheckTriple(uint8_t *base, uint32_t len) {
	EverParseErrorFrame frame;
	frame.filled = FALSE;
	uint64_t result = DerivedValidateTriple( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			DerivedEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN DerivedCheckQuad(uint8_t *base, uint32_t len) {
	EverParseErrorFrame frame;
	frame.filled = FALSE;
	uint64_t result = DerivedValidateQuad( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			DerivedEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
