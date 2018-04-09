module Parse_ticketFlags

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type ticketFlags' =
  | Allow_early_data
  | Allow_dhe_resumption
  | Allow_psk_resumption
  | Unknown_ticketFlags of (v:U32.t{not (L.mem v [1ul; 2ul; 4ul])})

type ticketFlags = v:ticketFlags'{~(Unknown_ticketFlags? v)}

inline_for_extraction val ticketFlags_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let ticketFlags_parser_kind = LP.strong_parser_kind 4 4 ticketFlags_parser_kind_metadata

inline_for_extraction val ticketFlags_parser: LP.parser ticketFlags_parser_kind ticketFlags
inline_for_extraction val ticketFlags_parser32: LP.parser32 ticketFlags_parser

inline_for_extraction val ticketFlags_serializer: LP.serializer ticketFlags_parser
inline_for_extraction val ticketFlags_serializer32: LP.serializer32 ticketFlags_serializer

