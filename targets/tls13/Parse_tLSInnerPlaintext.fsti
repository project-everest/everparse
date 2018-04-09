module Parse_tLSInnerPlaintext

open FStar.Bytes
open Parse_contentType

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type tLSInnerPlaintext = {
	type : contentType;
}

val bytesize: tLSInnerPlaintext -> nat

inline_for_extraction val tLSInnerPlaintext_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let tLSInnerPlaintext_parser_kind = LP.strong_parser_kind 3 3 tLSInnerPlaintext_parser_kind_metadata

val tLSInnerPlaintext_parser: LP.parser tLSInnerPlaintext_parser_kind tLSInnerPlaintext

inline_for_extraction val tLSInnerPlaintext_parser32: LP.parser32 tLSInnerPlaintext_parser

val tLSInnerPlaintext_serializer: LP.serializer tLSInnerPlaintext_parser

inline_for_extraction val tLSInnerPlaintext_serializer32: LP.serializer32 tLSInnerPlaintext_serializer

