module Parse_certificateRequest

open FStar.Bytes
open Parse_signatureScheme
open Parse_distinguishedName
open Parse_certificateExtension

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type certificateRequest_supported_signature_algorithms = l:list signatureScheme{1 <= L.length l /\ L.length l <= 32767}

type certificateRequest_certificate_authorities = l:list distinguishedName{0 <= L.length l /\ L.length l <= 21845}

type certificateRequest_certificate_extensions = l:list certificateExtension{0 <= L.length l /\ L.length l <= 16383}

type certificateRequest = {
	certificate_request_context : b:bytes{0 <= length b /\ length b <= 255};
	supported_signature_algorithms : certificateRequest_supported_signature_algorithms;
	certificate_authorities : certificateRequest_certificate_authorities;
	certificate_extensions : certificateRequest_certificate_extensions;
}

val bytesize: certificateRequest -> nat

inline_for_extraction val certificateRequest_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let certificateRequest_parser_kind = LP.strong_parser_kind 9 196866 certificateRequest_parser_kind_metadata

val certificateRequest_parser: LP.parser certificateRequest_parser_kind certificateRequest

inline_for_extraction val certificateRequest_parser32: LP.parser32 certificateRequest_parser

val certificateRequest_serializer: LP.serializer certificateRequest_parser

inline_for_extraction val certificateRequest_serializer32: LP.serializer32 certificateRequest_serializer

