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
	BOOLEAN result = FALSE;
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t ep_status = GotoReturnValidatePoint( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			GotoReturnEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		goto exit;
	}
	result = TRUE;

exit:
	return result;
}

static BOOLEAN GotoReturnCheckTagged(uint64_t bound, uint8_t *base, uint32_t len) {
	BOOLEAN result = FALSE;
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t ep_status = GotoReturnValidateTagged(bound,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			GotoReturnEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		goto exit;
	}
	result = TRUE;

exit:
	return result;
}

uint32_t GotoReturnProbeInPlaceCheckTagged(uint64_t bound, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint32_t result = EVERPARSE_PROBE_FAILURE_INIT;

	if(providedSize < 42U)
	{

		//
		// Not enough space for probe
		//

		result = EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
		goto exit;
	}
	if(!ProbeInit("GotoReturnCheckTagged", 42U, probeDest))
	{

		//
		// ProbeInit failed
		//

		result = EVERPARSE_PROBE_FAILURE_INIT;
		goto exit;
	}
	if (!ProbeInPlace(42U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		result = EVERPARSE_PROBE_FAILURE_PROBE;
		goto exit;
	}
	uint8_t *base = EverParseStreamOf(probeDest);
	if (!GotoReturnCheckTagged(bound,  base, 42U))
	{
		result = EVERPARSE_PROBE_FAILURE_VALIDATION;
		goto exit;
	}
	result = EVERPARSE_SUCCESS;

exit:
	return result;
}
