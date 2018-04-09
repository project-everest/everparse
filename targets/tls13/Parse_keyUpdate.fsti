module Parse_keyUpdate

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type keyUpdate = {
}

inline_for_extraction val keyUpdate_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let keyUpdate_parser_kind = LP.strong_parser_kind 0 0 keyUpdate_parser_kind_metadata

val keyUpdate_parser: LP.parser keyUpdate_parser_kind keyUpdate

inline_for_extraction val keyUpdate_parser32: LP.parser32 keyUpdate_parser

val keyUpdate_serializer: LP.serializer keyUpdate_parser

inline_for_extraction val keyUpdate_serializer32: LP.serializer32 keyUpdate_serializer

