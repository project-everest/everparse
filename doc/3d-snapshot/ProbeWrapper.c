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

BOOLEAN ProbeProbeAndCopyCheckIndirect(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr) {
	if(!ProbeInit("ProbeCheckIndirect", 9U, probeDest))
    {
      // ProbeInit failed
      return FALSE;
    }
    if (ProbeAndCopy(9U, 0, 0, probeAddr, probeDest))
    {
      uint8_t * base = EverParseStreamOf(probeDest);
      return ProbeCheckIndirect( base, 9U);
    } 
    else
    {
      // we currently assume that the probe function handles its own error
      return FALSE;
    }
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

BOOLEAN ProbeProbeAndCopyCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr) {
	if(!ProbeInit("ProbeCheckMultiProbe", 25U, probeDest))
    {
      // ProbeInit failed
      return FALSE;
    }
    if (ProbeAndCopy(25U, 0, 0, probeAddr, probeDest))
    {
      uint8_t * base = EverParseStreamOf(probeDest);
      return ProbeCheckMultiProbe(destT1, destT2,  base, 25U);
    } 
    else
    {
      // we currently assume that the probe function handles its own error
      return FALSE;
    }
}

BOOLEAN ProbeProbeAndCopyAltCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr) {
	if(!ProbeInit("ProbeCheckMultiProbe", 25U, probeDest))
    {
      // ProbeInit failed
      return FALSE;
    }
    if (ProbeAndCopyAlt(25U, 0, 0, probeAddr, probeDest))
    {
      uint8_t * base = EverParseStreamOf(probeDest);
      return ProbeCheckMultiProbe(destT1, destT2,  base, 25U);
    } 
    else
    {
      // we currently assume that the probe function handles its own error
      return FALSE;
    }
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
