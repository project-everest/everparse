module Parse_namedGroup

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type namedGroup' =
  | Secp256r1
  | Secp384r1
  | Secp521r1
  | X25519
  | X448
  | Ffdhe2048
  | Ffdhe3072
  | Ffdhe4096
  | Ffdhe6144
  | Ffdhe8192
  | Unknown_namedGroup of (v:U16.t{not (L.mem v [23us; 24us; 25us; 29us; 30us; 256us; 257us; 258us; 259us; 260us])})

type namedGroup = v:namedGroup'{~(Unknown_namedGroup? v)}

inline_for_extraction val namedGroup_parser_kind_metadata : LP.parser_kind_metadata_t
inline_for_extraction let namedGroup_parser_kind = LP.strong_parser_kind 2 2 namedGroup_parser_kind_metadata

inline_for_extraction val namedGroup_parser: LP.parser namedGroup_parser_kind namedGroup
inline_for_extraction val namedGroup_parser32: LP.parser32 namedGroup_parser

inline_for_extraction val namedGroup_serializer: LP.serializer namedGroup_parser
inline_for_extraction val namedGroup_serializer32: LP.serializer32 namedGroup_serializer

