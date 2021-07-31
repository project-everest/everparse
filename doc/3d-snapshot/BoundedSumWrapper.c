#include "BoundedSumWrapper.h"
#include "EverParse.h"
#include "BoundedSum.h"
void BoundedSumEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename,
	const char *fieldname,
	const char *reason,
	uint8_t *context,
	EverParseInputBuffer input,
	uint32_t start_pos)
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

BOOLEAN BoundedSumCheckBoundedSum(uint32_t bound, uint8_t *base, uint32_t len) {
	EverParseErrorFrame frame;
	frame.filled = FALSE;
	EverParseInputBuffer input = EverParseMakeInputBuffer(base, len);
	uint64_t result = BoundedSumValidateBoundedSum(bound,  (uint8_t*)&frame, &DefaultErrorHandler, input, 0);
	if (EverParseResultIsError(result))
	{
		if (frame.filled)
		{
			BoundedSumEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN BoundedSumCheckMySum(uint8_t *base, uint32_t len) {
	EverParseErrorFrame frame;
	frame.filled = FALSE;
	EverParseInputBuffer input = EverParseMakeInputBuffer(base, len);
	uint64_t result = BoundedSumValidateMySum( (uint8_t*)&frame, &DefaultErrorHandler, input, 0);
	if (EverParseResultIsError(result))
	{
		if (frame.filled)
		{
			BoundedSumEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
