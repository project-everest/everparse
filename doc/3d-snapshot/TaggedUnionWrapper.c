#include "TaggedUnionWrapper.h"
#include "EverParse.h"
#include "TaggedUnion.h"
void TaggedUnionEverParseError(const char *StructName, const char *FieldName, const char *Reason);

typedef struct _ErrorFrame
{
	BOOLEAN filled;
	uint32_t start_pos;
	const char *typename;
	const char *fieldname;
	const char *reason;
} ErrorFrame;

static
void DefaultErrorHandler(
	const char *typename,
	const char *fieldname,
	const char *reason,
	uint8_t *context,
	EverParseInputBuffer input,
	uint32_t start_pos)
{
	ErrorFrame *frame = (ErrorFrame*)context;
	if (!frame->filled)
	{
		frame->filled = TRUE;
		frame->start_pos = start_pos;
		frame->typename = typename;
		frame->fieldname = fieldname;
		frame->reason = reason;
	}
}

BOOLEAN TaggedUnionCheckInteger(uint8_t *base, uint32_t len) {
	ErrorFrame frame;
	frame.filled = FALSE;
	uint32_t position = 0;
	EverParseInputBuffer input = EverParseMakeInputBuffer(base, len, &position);
	uint64_t result = TaggedUnionValidateInteger( (uint8_t*)&frame, &DefaultErrorHandler, input);
	if (EverParseResultIsError(result))
	{
		if (frame.filled)
		{
			TaggedUnionEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
