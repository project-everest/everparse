module Parse_distinguishedName

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type distinguishedName = {
	dn : b:bytes{1 <= length b /\ length b <= 65535};
}

val bytesize: distinguishedName -> nat

inline_for_extraction val distinguishedName_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let distinguishedName_parser_kind = LP.strong_parser_kind 3 65537 distinguishedName_parser_kind_metadata

val distinguishedName_parser: LP.parser distinguishedName_parser_kind distinguishedName

inline_for_extraction val distinguishedName_parser32: LP.parser32 distinguishedName_parser

val distinguishedName_serializer: LP.serializer distinguishedName_parser

inline_for_extraction val distinguishedName_serializer32: LP.serializer32 distinguishedName_serializer

