module LowParse.Spec.VLData
include LowParse.Spec.FLData
include LowParse.Spec.AllIntegers // for bounded_integer, in_bounds, etc.

module Seq = FStar.Seq
module U32 = FStar.UInt32
module M = LowParse.Math

#reset-options "--z3rlimit 64 --max_fuel 64 --max_ifuel 64 --z3refresh --z3cliopt smt.arith.nl=false"

let parse_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_vldata_gen_kind sz k) t)
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz k;
  and_then
    #_
    #(parse_filter_refine #(bounded_integer sz) f)
    (parse_filter #_ #(bounded_integer sz) (parse_bounded_integer sz) f)
    #_
    #t
    (parse_vldata_payload sz f p)

let parse_vldata_gen_eq_def
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vldata_payload sz f p) /\
  parse_vldata_gen_kind sz k == and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz k) /\
  parse_vldata_gen sz f p ==
  and_then
    #_
    #(parse_filter_refine #(bounded_integer sz) f)
    (parse_filter #_ #(bounded_integer sz) (parse_bounded_integer sz) f)
    #_
    #t
    (parse_vldata_payload sz f p))
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz k
