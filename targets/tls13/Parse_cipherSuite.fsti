module Parse_cipherSuite

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type cipherSuite_cs = l:list U8.t

type cipherSuite = {
	cs : cipherSuite_cs;
}

inline_for_extraction val cipherSuite_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let cipherSuite_parser_kind = LP.strong_parser_kind 2 2 cipherSuite_parser_kind_metadata

val cipherSuite_parser: LP.parser cipherSuite_parser_kind cipherSuite

inline_for_extraction val cipherSuite_parser32: LP.parser32 cipherSuite_parser

val cipherSuite_serializer: LP.serializer cipherSuite_parser

inline_for_extraction val cipherSuite_serializer32: LP.serializer32 cipherSuite_serializer

inline_for_extraction val cipherSuite_size32: LP.size32 cipherSuite_serializer
