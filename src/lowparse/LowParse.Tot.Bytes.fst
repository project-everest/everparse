module LowParse.Tot.Bytes
include LowParse.Spec.Bytes
include LowParse.Tot.Combinators
include LowParse.Tot.Int

inline_for_extraction
let parse_all_bytes = tot_parse_all_bytes
