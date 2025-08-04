module Parquet.Spec.Jump
include LowParse.Spec.Base

open LowParse.Spec.FLData

module Seq = FStar.Seq

let coerce_ 
  (#t: Type)
  (#new_b: bytes)
  (#b: bytes { Seq.length b >= Seq.length new_b })
  (x: option (t & consumed_length new_b))
: option (t & consumed_length b)
  = match x with
    | None -> None
    | Some (v, l) -> Some (v, l)

val jump_with_offset_and_size_then_parse
  (offset: nat)
  (size: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
// : Tot (parser (parse_fldata_kind size k) t)
: Tot (bare_parser t)

let jump_with_offset_and_size_then_parse
  (offset: nat)
  (size: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (bare_parser t)
// : Tot (parser (parse_fldata_kind size k) t)
  = fun b ->
    if Seq.length b < offset + size then
      None
    else
      let new_b = Seq.slice b offset (offset + size) in
      coerce_ (parse (parse_fldata p size) new_b)
