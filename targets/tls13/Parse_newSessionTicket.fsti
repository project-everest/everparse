module Parse_newSessionTicket

open FStar.Bytes
open Parse_ticketExtension

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type newSessionTicket_extensions = l:list ticketExtension{0 <= L.length l /\ L.length l <= 13106}

type newSessionTicket = {
	ticket_lifetime : U32.t;
	flags : U32.t;
	ticket_age_add : U32.t;
	extensions : newSessionTicket_extensions;
	ticket : b:bytes{1 <= length b /\ length b <= 65535};
}

val bytesize: newSessionTicket -> nat

inline_for_extraction val newSessionTicket_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction let newSessionTicket_parser_kind = LP.strong_parser_kind 17 131085 newSessionTicket_parser_kind_metadata

val newSessionTicket_parser: LP.parser newSessionTicket_parser_kind newSessionTicket

inline_for_extraction val newSessionTicket_parser32: LP.parser32 newSessionTicket_parser

val newSessionTicket_serializer: LP.serializer newSessionTicket_parser

inline_for_extraction val newSessionTicket_serializer32: LP.serializer32 newSessionTicket_serializer

