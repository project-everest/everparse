#include "GotoReturnWrapper.h"
#include "EverParse.h"
#include "GotoReturn.h"
#include "EverParsePulse.h"
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(size_t) >= sizeof(uint32_t), "EverParse: size_t must be at least as wide as uint32_t");
_Static_assert(sizeof(size_t) >= sizeof(uint64_t), "EverParse: size_t must be at least as wide as uint64_t");
#endif
#include "GotoReturn_ExternalAPI.h"

void GotoReturnEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename_s,
	const char *fieldname,
	const char *reason,
	uint8_t error_code,
	uint8_t *context,
	uint8_t *base,
	size_t len,
	size_t *pos)
{
	EVERPARSE_ERROR_FRAME *frame = (EVERPARSE_ERROR_FRAME*)context;
	(void) len;
	EverParseDefaultErrorHandler(
		typename_s,
		fieldname,
		reason,
		(uint64_t)error_code,
		frame,
		base,
		(uint64_t)*pos
	);
}

BOOLEAN GotoReturnCheckPoint(uint8_t *base, uint32_t len) {
	BOOLEAN result = FALSE;
	EVERPARSE_ERROR_FRAME frame;
	size_t everparse_pos;
	uint8_t ep_status;

	frame.filled = FALSE;
	everparse_pos = (size_t)0U;
	ep_status = GotoReturnValidatePoint( (uint8_t*)&frame, &DefaultErrorHandler, base, (size_t)len, &everparse_pos);

	if (ep_status != 0U)
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
	size_t everparse_pos;
	uint8_t ep_status;

	frame.filled = FALSE;
	everparse_pos = (size_t)0U;
	ep_status = GotoReturnValidateTagged(bound,  (uint8_t*)&frame, &DefaultErrorHandler, base, (size_t)len, &everparse_pos);

	if (ep_status != 0U)
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
