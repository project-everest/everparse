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
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateS(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
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
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateU(destS, destT,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
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
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateV(destS, destT,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

static BOOLEAN ProbeCheckIndirect(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateIndirect( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
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
	uint8_t *base;

	if(providedSize < 9U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckIndirect", 9U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(9U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!ProbeCheckIndirect( base, 9U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN ProbeCheckI(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateI(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

static BOOLEAN ProbeCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateMultiProbe(destT1, destT2,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
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
	uint8_t *base;

	if(providedSize < 25U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckMultiProbe", 25U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(25U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!ProbeCheckMultiProbe(destT1, destT2,  base, 25U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

uint32_t ProbeProbeAndCopyAltCheckMultiProbe(EVERPARSE_COPY_BUFFER_T destT1, EVERPARSE_COPY_BUFFER_T destT2, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint8_t *base;

	if(providedSize < 25U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckMultiProbe", 25U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopyAlt(25U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!ProbeCheckMultiProbe(destT1, destT2,  base, 25U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN ProbeCheckMaybeT(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateMaybeT(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
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
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateCoercePtr(dest,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

static BOOLEAN ProbeCheckProbeOnly(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateProbeOnly( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

uint32_t ProbeProbeAndCopyCheckProbeOnly(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint8_t *base;

	if(providedSize < 8U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckProbeOnly", 8U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(8U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!ProbeCheckProbeOnly( base, 8U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN ProbeCheckBothEntrypoints(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateBothEntrypoints( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

uint32_t ProbeProbeAndCopyCheckBothEntrypoints(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint8_t *base;

	if(providedSize < 8U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckBothEntrypoints", 8U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(8U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!ProbeCheckBothEntrypoints( base, 8U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN ValidateMyData(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateNamedPlainEp( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

static BOOLEAN ProbeCheckNamedProbeEp(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateNamedProbeEp( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

uint32_t ProbeMyData(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint8_t *base;

	if(providedSize < 8U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("ProbeCheckNamedProbeEp", 8U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(8U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!ProbeCheckNamedProbeEp( base, 8U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}

BOOLEAN CheckAll(uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	uint64_t ep_status;

	frame.filled = FALSE;
	ep_status = ProbeValidateNamedBothEp( (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);

	if (EverParseIsError(ep_status))
	{
		if (frame.filled)
		{
			ProbeEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

uint32_t ProbeAll(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize) {
	uint8_t *base;

	if(providedSize < 8U)
	{

		//
		// Not enough space for probe
		//

		return EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE;
	}
	if(!ProbeInit("CheckAll", 8U, probeDest))
	{

		//
		// ProbeInit failed
		//

		return EVERPARSE_PROBE_FAILURE_INIT;
	}
	if (!ProbeAndCopy(8U, 0, 0, probeAddr, probeDest))
	{

		//
		// Probe failed
		//

		return EVERPARSE_PROBE_FAILURE_PROBE;
	}
	base = EverParseStreamOf(probeDest);
	if (!CheckAll( base, 8U))
	{
		return EVERPARSE_PROBE_FAILURE_VALIDATION;
	}
	return EVERPARSE_SUCCESS;
}
