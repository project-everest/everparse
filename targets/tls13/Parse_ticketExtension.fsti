module Parse_ticketExtension

open FStar.Bytes
open Parse_ticketExtensionType

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type ticketExtension = {
	extension_type : ticketExtensionType;
	extension_data : b:bytes{1 <= length b /\ length b <= 65535};
}

val bytesize: ticketExtension -> nat

inline_for_extraction val ticketExtension_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let ticketExtension_parser_kind = LP.strong_parser_kind 5 65539 ticketExtension_parser_kind_metadata

val ticketExtension_parser: LP.parser ticketExtension_parser_kind ticketExtension

inline_for_extraction val ticketExtension_parser32: LP.parser32 ticketExtension_parser

val ticketExtension_serializer: LP.serializer ticketExtension_parser

inline_for_extraction val ticketExtension_serializer32: LP.serializer32 ticketExtension_serializer

