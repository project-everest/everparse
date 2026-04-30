#include "GotoReturnWrapper.h"
#include "EverParse.h"
#include "GotoReturn.h"
#include "GotoReturn_ExternalAPI.h"
void GotoReturnEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename_s,
	const char *fieldname,
	const char *reason,
	uint64_t error_code,
	uint8_t *context,
	EVERPARSE_INPUT_BUFFER input,
	uint64_t start_pos)
{
	EVERPARSE_ERROR_FRAME *frame = (EVERPARSE_ERROR_FRAME*)context;
	EverParseDefaultErrorHandler(
		typename_s,
		fieldname,
		reason,
		error_code,
		frame,
		input,
		start_pos
	);
}

BOOLEAN GotoReturnCheckPoint(uint8_t *base, uint32_t len) {
	BOOLEAN result__ = FALSE;
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = GotoReturnValidatePoint( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			GotoReturnEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		goto exit;
	}
	result__ = TRUE;
exit:
	return result__;
}

static BOOLEAN GotoReturnCheckTagged(uint64_t bound, uint8_t *base, uint32_t len) {
	BOOLEAN result__ = FALSE;
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = GotoReturnValidateTagged(bound,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			GotoReturnEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		goto exit;
	}
	result__ = TRUE;
exit:
	return result__;
}

uint32_t GotoReturnProbeInPlaceCheckTagged(uint64_t bound, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint32_t result__ = EVERPARSE_PROBE_FAILURE_UNIMPLEMENTED;
	if(providedSize < 42U)
	{
		// Not enough space for probe
		result__ = EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
		goto exit;
	}
	if(!ProbeInit("GotoReturnCheckTagged", 42U, probeDest))
	{
		// ProbeInit failed
		result__ = EVERPARSE_PROBE_FAILURE_INIT;
		goto exit;
	}
	if (!ProbeInPlace(42U, 0, 0, probeAddr, probeDest))
	{
		// Probe failed
		result__ = EVERPARSE_PROBE_FAILURE_PROBE;
		goto exit;
	}
	uint8_t *base = EverParseStreamOf(probeDest);
	if (!GotoReturnCheckTagged(bound,  base, 42U))
	{
		result__ = EVERPARSE_PROBE_FAILURE_VALIDATION;
		goto exit;
	}
	result__ = EVERPARSE_SUCCESS;
exit:
	return result__;
}
