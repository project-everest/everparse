#include "SpecializeDep1Wrapper.h"
#include "EverParse.h"
#include "SpecializeDep1.h"

void SpecializeDep1EverParseError(const char *StructName, const char *FieldName, const char *Reason);

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

BOOLEAN SpecializeDep1CheckEntry(BOOLEAN ___Requestor32, uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = SpecializeDep1ValidateEntry(___Requestor32, ___Len, ___Output,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			SpecializeDep1EverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN SpecializeDep1CheckCompleteEntry(BOOLEAN ___Requestor32, uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = SpecializeDep1ValidateEntry(___Requestor32, ___Len, ___Output,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			SpecializeDep1EverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	if (EverParseGetValidatorErrorPos(epStatus) != (uint64_t)len)
	{
		SpecializeDep1EverParseError("_ENTRY", "", "unexpected trailing bytes");
		return FALSE;
	}
	return TRUE;
}
