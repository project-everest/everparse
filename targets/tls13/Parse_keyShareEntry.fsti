module Parse_keyShareEntry

open FStar.Bytes
open Parse_namedGroup

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type keyShareEntry = {
	group : namedGroup;
	key_exchange : b:bytes{1 <= length b /\ length b <= 65535};
}

val bytesize: keyShareEntry -> nat

inline_for_extraction val keyShareEntry_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let keyShareEntry_parser_kind = LP.strong_parser_kind 5 65539 keyShareEntry_parser_kind_metadata

val keyShareEntry_parser: LP.parser keyShareEntry_parser_kind keyShareEntry

inline_for_extraction val keyShareEntry_parser32: LP.parser32 keyShareEntry_parser

val keyShareEntry_serializer: LP.serializer keyShareEntry_parser

inline_for_extraction val keyShareEntry_serializer32: LP.serializer32 keyShareEntry_serializer

