module LowParse.Spec.Parquet
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq

open LowParse.Spec.Base
open LowParse.Spec.RtoLDepPair
open LowParse.Spec.RtoLPair
open LowParse.Spec.Combinators // filter
open LowParse.Spec.SeqBytes // "PAR1"
open LowParse.Spec.BoundedInt // parse_u32_le

assume val parse_footer_kind: parser_kind
assume val footer_t: Type0
assume val parse_footer: parser parse_footer_kind footer_t

assume val parse_pages_kind: parser_kind
assume val pages_t: (footer: footer_t) -> Type0
assume val parse_pages: (footer: footer_t) -> parser parse_pages_kind (pages_t footer)

let is_PAR1 (s: Seq.lseq byte 4) : bool =
    let v0 = Seq.index s 0 in
    let v1 = Seq.index s 1 in
    let v2 = Seq.index s 2 in
    let v3 = Seq.index s 3 in
    (U32.v (FStar.Char.u32_of_char 'P') = U8.v v0)
    && (U32.v (FStar.Char.u32_of_char 'A') = U8.v v1)
    && (U32.v (FStar.Char.u32_of_char 'R') = U8.v v2)
    && (U32.v (FStar.Char.u32_of_char '1') = U8.v v3)


let parse_parquet  =
  parse_nondep_then_rtol
    (parse_filter (parse_seq_flbytes 4) is_PAR1)
    (parse_dtuple2_rtol
      parse_u32_le
      fun len -> (
        weaken (dtuple2_rtol_kind parse_seq_all_bytes_kind 0) (parse_dtuple2_rtol
          (parse_fldata parse_footer (U32.v len))
          fun footer -> (
            parse_seq_all_bytes
            // parse_pages footer
          ))
      )
    )
  
