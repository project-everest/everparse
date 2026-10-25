module LowParse.Tot.SeqBytes
include LowParse.Spec.SeqBytes
include LowParse.Tot.Combinators
include LowParse.Tot.Int

inline_for_extraction
let parse_seq_all_bytes = tot_parse_seq_all_bytes
