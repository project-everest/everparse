module Parse_handshake

open FStar.Bytes
open Parse_handshakeType

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type handshake = {
	msg_type : handshakeType;
	length : U32.t;
}

inline_for_extraction val handshake_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let handshake_parser_kind = LP.strong_parser_kind 4 4 handshake_parser_kind_metadata

val handshake_parser: LP.parser handshake_parser_kind handshake

inline_for_extraction val handshake_parser32: LP.parser32 handshake_parser

val handshake_serializer: LP.serializer handshake_parser

inline_for_extraction val handshake_serializer32: LP.serializer32 handshake_serializer

