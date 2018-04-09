module Parse_certificateExtension

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type certificateExtension = {
	certificate_extension_oid : b:bytes{1 <= length b /\ length b <= 255};
	certificate_extension_values : b:bytes{0 <= length b /\ length b <= 65535};
}

val bytesize: certificateExtension -> nat

inline_for_extraction val certificateExtension_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let certificateExtension_parser_kind = LP.strong_parser_kind 4 65793 certificateExtension_parser_kind_metadata

val certificateExtension_parser: LP.parser certificateExtension_parser_kind certificateExtension

inline_for_extraction val certificateExtension_parser32: LP.parser32 certificateExtension_parser

val certificateExtension_serializer: LP.serializer certificateExtension_parser

inline_for_extraction val certificateExtension_serializer32: LP.serializer32 certificateExtension_serializer

