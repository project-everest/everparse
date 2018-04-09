module Parse_certificate

open FStar.Bytes
open Parse_aSN1Cert

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type certificate_certificate_list = l:list aSN1Cert{0 <= L.length l /\ L.length l <= 4194303}

type certificate = {
	certificate_request_context : b:bytes{0 <= length b /\ length b <= 255};
	certificate_list : certificate_certificate_list;
}

val bytesize: certificate -> nat

inline_for_extraction val certificate_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let certificate_parser_kind = LP.strong_parser_kind 4 16777474 certificate_parser_kind_metadata

val certificate_parser: LP.parser certificate_parser_kind certificate

inline_for_extraction val certificate_parser32: LP.parser32 certificate_parser

val certificate_serializer: LP.serializer certificate_parser

inline_for_extraction val certificate_serializer32: LP.serializer32 certificate_serializer

