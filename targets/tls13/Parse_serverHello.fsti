module Parse_serverHello

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

type serverHello_extensions = l:list extension{0 <= L.length l /\ L.length l <= 16383}

type serverHello = {
	server_version : protocolVersion;
	random : random;
	cipher_suite : cipherSuite;
	extensions : serverHello_extensions;
}

val bytesize: serverHello -> nat

inline_for_extraction val serverHello_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let serverHello_parser_kind = LP.strong_parser_kind 38 65573 serverHello_parser_kind_metadata

val serverHello_parser: LP.parser serverHello_parser_kind serverHello

inline_for_extraction val serverHello_parser32: LP.parser32 serverHello_parser

val serverHello_serializer: LP.serializer serverHello_parser

inline_for_extraction val serverHello_serializer32: LP.serializer32 serverHello_serializer

