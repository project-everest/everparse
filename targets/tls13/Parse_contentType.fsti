module Parse_contentType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type contentType' =
  | Alert
  | Handshake
  | Application_data
  | Unknown_contentType of (v:U8.t{not (L.mem v [21z; 22z; 23z])})

type contentType = v:contentType'{~(Unknown_contentType? v)}

inline_for_extraction val contentType_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let contentType_parser_kind = LP.strong_parser_kind 1 1 contentType_parser_kind_metadata

inline_for_extraction val contentType_parser: LP.parser contentType_parser_kind contentType
inline_for_extraction val contentType_parser32: LP.parser32 contentType_parser

inline_for_extraction val contentType_serializer: LP.serializer contentType_parser
inline_for_extraction val contentType_serializer32: LP.serializer32 contentType_serializer

