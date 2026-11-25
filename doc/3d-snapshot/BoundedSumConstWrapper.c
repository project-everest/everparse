#include "BoundedSumConstWrapper.h"
#include "EverParse.h"
#include "BoundedSumConst.h"

void BoundedSumConstEverParseError(const char *StructName, const char *FieldName, const char *Reason);

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

BOOLEAN BoundedSumConstCheckBoundedSum(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = BoundedSumConstValidateBoundedSum( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			BoundedSumConstEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN BoundedSumConstCheckCompleteBoundedSum(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t epStatus = BoundedSumConstValidateBoundedSum( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(epStatus))
	{
		if (frame.filled)
		{
			BoundedSumConstEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	if (EverParseGetValidatorErrorPos(epStatus) != (uint64_t)len)
	{
		BoundedSumConstEverParseError("_boundedSum", "", "unexpected trailing bytes");
		return FALSE;
	}
	return TRUE;
}
