module Parse_extension

open FStar.Bytes
open Parse_extensionType

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type extension = {
	extension_type : extensionType;
	extension_data : b:bytes{0 <= length b /\ length b <= 65535};
}

val bytesize: extension -> nat

inline_for_extraction val extension_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let extension_parser_kind = LP.strong_parser_kind 4 65539 extension_parser_kind_metadata

val extension_parser: LP.parser extension_parser_kind extension

inline_for_extraction val extension_parser32: LP.parser32 extension_parser

val extension_serializer: LP.serializer extension_parser

inline_for_extraction val extension_serializer32: LP.serializer32 extension_serializer

