module Parse_aSN1Cert

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type aSN1Cert = {
	asn1 : b:bytes{1 <= length b /\ length b <= 16777215};
}

val bytesize: aSN1Cert -> nat

inline_for_extraction val aSN1Cert_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let aSN1Cert_parser_kind = LP.strong_parser_kind 4 16777218 aSN1Cert_parser_kind_metadata

val aSN1Cert_parser: LP.parser aSN1Cert_parser_kind aSN1Cert

inline_for_extraction val aSN1Cert_parser32: LP.parser32 aSN1Cert_parser

val aSN1Cert_serializer: LP.serializer aSN1Cert_parser

inline_for_extraction val aSN1Cert_serializer32: LP.serializer32 aSN1Cert_serializer

