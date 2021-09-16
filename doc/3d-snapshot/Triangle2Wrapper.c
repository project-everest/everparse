#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
void Triangle2EverParseError(const char *StructName, const char *FieldName, const char *Reason);

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

BOOLEAN Triangle2CheckTriangle(uint8_t *base, uint32_t len) {
	EverParseErrorFrame frame;
	frame.filled = FALSE;
	uint64_t result = Triangle2ValidateTriangle( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			Triangle2EverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
