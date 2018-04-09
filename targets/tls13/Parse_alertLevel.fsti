module Parse_alertLevel

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type alertLevel' =
  | Warning
  | Fatal
  | Unknown_alertLevel of (v:U8.t{not (L.mem v [1z; 2z])})

type alertLevel = v:alertLevel'{~(Unknown_alertLevel? v)}

inline_for_extraction val alertLevel_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let alertLevel_parser_kind = LP.strong_parser_kind 1 1 alertLevel_parser_kind_metadata

inline_for_extraction val alertLevel_parser: LP.parser alertLevel_parser_kind alertLevel
inline_for_extraction val alertLevel_parser32: LP.parser32 alertLevel_parser

inline_for_extraction val alertLevel_serializer: LP.serializer alertLevel_parser
inline_for_extraction val alertLevel_serializer32: LP.serializer32 alertLevel_serializer

