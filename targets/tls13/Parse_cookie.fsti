module Parse_cookie

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type cookie = {
	cookie : b:bytes{0 <= length b /\ length b <= 65535};
}

val bytesize: cookie -> nat

inline_for_extraction val cookie_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let cookie_parser_kind = LP.strong_parser_kind 2 65537 cookie_parser_kind_metadata

val cookie_parser: LP.parser cookie_parser_kind cookie

inline_for_extraction val cookie_parser32: LP.parser32 cookie_parser

val cookie_serializer: LP.serializer cookie_parser

inline_for_extraction val cookie_serializer32: LP.serializer32 cookie_serializer

