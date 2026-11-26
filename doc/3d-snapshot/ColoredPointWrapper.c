#include "ColoredPointWrapper.h"
#include "EverParse.h"
#include "ColoredPoint.h"

void ColoredPointEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typeName,
	const char *fieldname,
	const char *reason,
	uint64_t errorCode,
	uint8_t *context,
	EVERPARSE_INPUT_BUFFER input,
	uint64_t startPos)
{
	EVERPARSE_ERROR_FRAME *frame = (EVERPARSE_ERROR_FRAME*)context;
	EverParseDefaultErrorHandler(
		typeName,
		fieldname,
		reason,
		errorCode,
		frame,
		input,
		startPos
	);
}

BOOLEAN ColoredPointCheckColoredPoint1(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = ColoredPointValidateColoredPoint1( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			ColoredPointEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ColoredPointCheckCompleteColoredPoint1(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = ColoredPointValidateColoredPoint1( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			ColoredPointEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	if (EverParseGetValidatorErrorPos(epStatus) != (uint64_t)len)
	{
		ColoredPointEverParseError("_coloredPoint1", "", "unexpected trailing bytes");
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ColoredPointCheckColoredPoint2(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = ColoredPointValidateColoredPoint2( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			ColoredPointEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ColoredPointCheckCompleteColoredPoint2(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = ColoredPointValidateColoredPoint2( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			ColoredPointEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	if (EverParseGetValidatorErrorPos(epStatus) != (uint64_t)len)
	{
		ColoredPointEverParseError("_coloredPoint2", "", "unexpected trailing bytes");
		return FALSE;
	}
	return TRUE;
}
