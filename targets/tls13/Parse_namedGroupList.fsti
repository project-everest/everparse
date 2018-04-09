module Parse_namedGroupList

open FStar.Bytes
open Parse_namedGroup

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type namedGroupList_named_group_list = l:list namedGroup{1 <= L.length l /\ L.length l <= 32767}

type namedGroupList = {
	named_group_list : namedGroupList_named_group_list;
}

val bytesize: namedGroupList -> nat

inline_for_extraction val namedGroupList_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let namedGroupList_parser_kind = LP.strong_parser_kind 4 65537 namedGroupList_parser_kind_metadata

val namedGroupList_parser: LP.parser namedGroupList_parser_kind namedGroupList

inline_for_extraction val namedGroupList_parser32: LP.parser32 namedGroupList_parser

val namedGroupList_serializer: LP.serializer namedGroupList_parser

inline_for_extraction val namedGroupList_serializer32: LP.serializer32 namedGroupList_serializer

