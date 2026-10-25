module LowParse.Tot.Int
include LowParse.Spec.Int
include LowParse.Tot.Base

inline_for_extraction
let parse_u8 = tot_parse_u8

val serialize_u8 : serializer parse_u8
let serialize_u8 =
  serialize_ext _ serialize_u8 _
