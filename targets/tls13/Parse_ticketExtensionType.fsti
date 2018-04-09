module Parse_ticketExtensionType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type ticketExtensionType' =
  | Unknown_ticketExtensionType of (v:U16.t{not (L.mem v [True])})

type ticketExtensionType = v:ticketExtensionType'{~(Unknown_ticketExtensionType? v)}

inline_for_extraction val ticketExtensionType_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let ticketExtensionType_parser_kind = LP.strong_parser_kind 2 2 ticketExtensionType_parser_kind_metadata

inline_for_extraction val ticketExtensionType_parser: LP.parser ticketExtensionType_parser_kind ticketExtensionType
inline_for_extraction val ticketExtensionType_parser32: LP.parser32 ticketExtensionType_parser

inline_for_extraction val ticketExtensionType_serializer: LP.serializer ticketExtensionType_parser
inline_for_extraction val ticketExtensionType_serializer32: LP.serializer32 ticketExtensionType_serializer

