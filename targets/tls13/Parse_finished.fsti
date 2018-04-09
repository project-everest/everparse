module Parse_finished

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type finished = {
}

val bytesize: finished -> nat

inline_for_extraction val finished_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let finished_parser_kind = LP.strong_parser_kind 1 1 finished_parser_kind_metadata

val finished_parser: LP.parser finished_parser_kind finished

inline_for_extraction val finished_parser32: LP.parser32 finished_parser

val finished_serializer: LP.serializer finished_parser

inline_for_extraction val finished_serializer32: LP.serializer32 finished_serializer

