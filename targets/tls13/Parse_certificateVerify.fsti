module Parse_certificateVerify

open FStar.Bytes
open Parse_signatureScheme

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type certificateVerify = {
	algorithm : signatureScheme;
	signature : b:bytes{0 <= length b /\ length b <= 65535};
}

val bytesize: certificateVerify -> nat

inline_for_extraction val certificateVerify_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let certificateVerify_parser_kind = LP.strong_parser_kind 4 65539 certificateVerify_parser_kind_metadata

val certificateVerify_parser: LP.parser certificateVerify_parser_kind certificateVerify

inline_for_extraction val certificateVerify_parser32: LP.parser32 certificateVerify_parser

val certificateVerify_serializer: LP.serializer certificateVerify_parser

inline_for_extraction val certificateVerify_serializer32: LP.serializer32 certificateVerify_serializer

