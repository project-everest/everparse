module LowParse.SteelST.Parse

let aparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
  ([@@@ smt_fallback] vp: v k t)
: Tot vprop
= aparse0 p a vp

let aparse_eq p a vp = ()
