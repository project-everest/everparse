#include "ProbeWrapper.h"
#include "EverParse.h"
#include "Probe.h"
#include "Probe_ExternalAPI.h"
void ProbeEverParseError(const char *StructName, const char *FieldName, const char *Reason);

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

BOOLEAN ProbeCheckS(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateS(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ProbeCheckU(EVERPARSE_COPY_BUFFER_T destS, EVERPARSE_COPY_BUFFER_T destT, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateU(destS, destT,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ProbeCheckV(EVERPARSE_COPY_BUFFER_T destS, EVERPARSE_COPY_BUFFER_T destT, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateV(destS, destT,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ProbeCheckIndirect(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateIndirect( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

uint32_t ProbeProbeAndCopyCheckIndirect(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	if(providedSize < 9U)
	{
		// Not enough space for probe
		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckIndirect", 9U, probeDest))
	{
		// ProbeInit failed
		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(9U, 0, 0, probeAddr, probeDest))
	{
		// Probe failed
		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	uint8_t * base = EverParseStreamOf(probeDest);
	if (!ProbeCheckIndirect( base, 9U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN ProbeCheckI(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateI(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ProbeCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateMultiProbe(destT1, destT2,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

uint32_t ProbeProbeAndCopyCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	if(providedSize < 25U)
	{
		// Not enough space for probe
		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckMultiProbe", 25U, probeDest))
	{
		// ProbeInit failed
		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(25U, 0, 0, probeAddr, probeDest))
	{
		// Probe failed
		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	uint8_t * base = EverParseStreamOf(probeDest);
	if (!ProbeCheckMultiProbe(destT1, destT2,  base, 25U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

uint32_t ProbeProbeAndCopyAltCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	if(providedSize < 25U)
	{
		// Not enough space for probe
		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckMultiProbe", 25U, probeDest))
	{
		// ProbeInit failed
		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopyAlt(25U, 0, 0, probeAddr, probeDest))
	{
		// Probe failed
		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	uint8_t * base = EverParseStreamOf(probeDest);
	if (!ProbeCheckMultiProbe(destT1, destT2,  base, 25U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN ProbeCheckMaybeT(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateMaybeT(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ProbeCheckCoercePtr(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ProbeValidateCoercePtr(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
