#include "Triangle2Wrapper.h"
#include "EverParse.h"
#include "Triangle2.h"
#include "EverParsePulse.h"
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(size_t) >= sizeof(uint32_t), "EverParse: size_t must be at least as wide as uint32_t");
_Static_assert(sizeof(size_t) <= sizeof(uint64_t), "EverParse: size_t must be no wider than uint64_t");
#endif

void Triangle2EverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename_s,
	const char *fieldname,
	const char *reason,
	uint8_t error_code,
	uint8_t *context,
	uint8_t *base,
	size_t len,
	size_t *pos,
	uint64_t start_pos)
{
	EVERPARSE_ERROR_FRAME *frame = (EVERPARSE_ERROR_FRAME*)context;
	(void) len;
	(void) pos;
	EverParseDefaultErrorHandler(
		typename_s,
		fieldname,
		reason,
		(uint64_t)error_code,
		frame,
		base,
		start_pos
	);
}

BOOLEAN Triangle2CheckTriangle(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	size_t everparse_pos;
	uint8_t ep_status;

	frame.filled = FALSE;
	everparse_pos = (size_t)0U;
	ep_status = Triangle2ValidateTriangle( (uint8_t*)&frame, &DefaultErrorHandler, base, (size_t)len, &everparse_pos);

	if (ep_status != 0U)
	{
		if (frame.filled)
		{
			Triangle2EverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN Triangle2CheckCompleteTriangle(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	size_t everparse_pos;
	uint8_t ep_status;

	frame.filled = FALSE;
	everparse_pos = (size_t)0U;
	ep_status = Triangle2ValidateTriangle( (uint8_t*)&frame, &DefaultErrorHandler, base, (size_t)len, &everparse_pos);

	if (ep_status != 0U)
	{
		if (frame.filled)
		{
			Triangle2EverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	if (everparse_pos != (size_t)len)
	{
		Triangle2EverParseError("_triangle", "", "unexpected trailing bytes");
		return FALSE;
	}
	return TRUE;
}
