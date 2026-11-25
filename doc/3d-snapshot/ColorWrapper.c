#include "ColorWrapper.h"
#include "EverParse.h"
#include "Color.h"

void ColorEverParseError(const char *StructName, const char *FieldName, const char *Reason);

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

BOOLEAN ColorCheckColoredPoint(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = ColorValidateColoredPoint( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			ColorEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ColorCheckCompleteColoredPoint(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = ColorValidateColoredPoint( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			ColorEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	if (EverParseGetValidatorErrorPos(epStatus) != (uint64_t)len)
	{
		ColorEverParseError("_coloredPoint", "", "unexpected trailing bytes");
		return FALSE;
	}
	return TRUE;
}
