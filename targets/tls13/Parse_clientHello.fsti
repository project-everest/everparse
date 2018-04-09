module Parse_clientHello

open FStar.Bytes
open Parse_protocolVersion
open Parse_random
open Parse_cipherSuite
open Parse_extension

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type clientHello_cipher_suites = l:list cipherSuite{1 <= L.length l /\ L.length l <= 32767}

type clientHello_extensions = l:list extension{0 <= L.length l /\ L.length l <= 16383}

type clientHello = {
	client_version : protocolVersion;
	random : random;
	legacy_session_id : b:bytes{0 <= length b /\ length b <= 32};
	cipher_suites : clientHello_cipher_suites;
	legacy_compression_methods : b:bytes{1 <= length b /\ length b <= 255};
	extensions : clientHello_extensions;
}

val bytesize: clientHello -> nat

inline_for_extraction val clientHello_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let clientHello_parser_kind = LP.strong_parser_kind 43 131396 clientHello_parser_kind_metadata

val clientHello_parser: LP.parser clientHello_parser_kind clientHello

inline_for_extraction val clientHello_parser32: LP.parser32 clientHello_parser

val clientHello_serializer: LP.serializer clientHello_parser

inline_for_extraction val clientHello_serializer32: LP.serializer32 clientHello_serializer

