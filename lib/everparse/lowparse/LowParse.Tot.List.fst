module LowParse.Tot.List
include LowParse.Spec.List
include LowParse.Tot.Combinators

inline_for_extraction
let parse_list #k #t = tot_parse_list #k #t

