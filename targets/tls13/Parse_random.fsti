module Parse_random

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type random_random_bytes = l:list opaque

type random = {
	random_bytes : random_random_bytes;
}

inline_for_extraction val random_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let random_parser_kind = LP.strong_parser_kind 32 32 random_parser_kind_metadata

val random_parser: LP.parser random_parser_kind random

inline_for_extraction val random_parser32: LP.parser32 random_parser

val random_serializer: LP.serializer random_parser

inline_for_extraction val random_serializer32: LP.serializer32 random_serializer

