module Parse_protocolVersion

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type protocolVersion = {
	major : U8.t;
	minor : U8.t;
}

inline_for_extraction val protocolVersion_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let protocolVersion_parser_kind = LP.strong_parser_kind 2 2 protocolVersion_parser_kind_metadata

val protocolVersion_parser: LP.parser protocolVersion_parser_kind protocolVersion

inline_for_extraction val protocolVersion_parser32: LP.parser32 protocolVersion_parser

val protocolVersion_serializer: LP.serializer protocolVersion_parser

inline_for_extraction val protocolVersion_serializer32: LP.serializer32 protocolVersion_serializer

