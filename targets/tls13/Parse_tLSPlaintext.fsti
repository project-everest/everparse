module Parse_tLSPlaintext

open FStar.Bytes
open Parse_contentType
open Parse_protocolVersion

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type tLSPlaintext = {
	type : contentType;
	record_version : protocolVersion;
	length : U16.t;
}

val bytesize: tLSPlaintext -> nat

inline_for_extraction val tLSPlaintext_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let tLSPlaintext_parser_kind = LP.strong_parser_kind 6 6 tLSPlaintext_parser_kind_metadata

val tLSPlaintext_parser: LP.parser tLSPlaintext_parser_kind tLSPlaintext

inline_for_extraction val tLSPlaintext_parser32: LP.parser32 tLSPlaintext_parser

val tLSPlaintext_serializer: LP.serializer tLSPlaintext_parser

inline_for_extraction val tLSPlaintext_serializer32: LP.serializer32 tLSPlaintext_serializer

