module Parse_helloRetryRequest

open FStar.Bytes
open Parse_protocolVersion
open Parse_cipherSuite
open Parse_namedGroup
open Parse_extension

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type helloRetryRequest_extensions = l:list extension{0 <= L.length l /\ L.length l <= 16383}

type helloRetryRequest = {
	server_version : protocolVersion;
	cipher_suite : cipherSuite;
	selected_group : namedGroup;
	extensions : helloRetryRequest_extensions;
}

val bytesize: helloRetryRequest -> nat

inline_for_extraction val helloRetryRequest_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let helloRetryRequest_parser_kind = LP.strong_parser_kind 8 65543 helloRetryRequest_parser_kind_metadata

val helloRetryRequest_parser: LP.parser helloRetryRequest_parser_kind helloRetryRequest

inline_for_extraction val helloRetryRequest_parser32: LP.parser32 helloRetryRequest_parser

val helloRetryRequest_serializer: LP.serializer helloRetryRequest_parser

inline_for_extraction val helloRetryRequest_serializer32: LP.serializer32 helloRetryRequest_serializer

