module Parse_extensionType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type extensionType' =
  | Supported_groups
  | Signature_algorithms
  | Key_share
  | Pre_shared_key
  | Early_data
  | Cookie
  | Unknown_extensionType of (v:U16.t{not (L.mem v [10us; 13us; 40us; 41us; 42us; 44us])})

type extensionType = v:extensionType'{~(Unknown_extensionType? v)}

inline_for_extraction val extensionType_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let extensionType_parser_kind = LP.strong_parser_kind 2 2 extensionType_parser_kind_metadata

inline_for_extraction val extensionType_parser: LP.parser extensionType_parser_kind extensionType
inline_for_extraction val extensionType_parser32: LP.parser32 extensionType_parser

inline_for_extraction val extensionType_serializer: LP.serializer extensionType_parser
inline_for_extraction val extensionType_serializer32: LP.serializer32 extensionType_serializer

