module Parse_tLSCiphertext

open FStar.Bytes
open Parse_contentType
open Parse_protocolVersion

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type tLSCiphertext = {
	opaque_type : contentType;
	record_version : protocolVersion;
	length : U16.t;
}

val bytesize: tLSCiphertext -> nat

inline_for_extraction val tLSCiphertext_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let tLSCiphertext_parser_kind = LP.strong_parser_kind 6 6 tLSCiphertext_parser_kind_metadata

val tLSCiphertext_parser: LP.parser tLSCiphertext_parser_kind tLSCiphertext

inline_for_extraction val tLSCiphertext_parser32: LP.parser32 tLSCiphertext_parser

val tLSCiphertext_serializer: LP.serializer tLSCiphertext_parser

inline_for_extraction val tLSCiphertext_serializer32: LP.serializer32 tLSCiphertext_serializer

