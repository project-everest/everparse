module LowParse.Pulse.Sum.Aux
#lang-pulse
open LowParse.Spec.Combinators
open LowParse.Spec.Enum
open LowParse.Spec.Sum
open LowParse.Pulse.Base
open LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

(* l2r_leaf_write_enum_key: write an enum key using the repr writer *)
inline_for_extraction
let l2r_leaf_write_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (#s: serializer p)
  (w: l2r_leaf_writer u#0 s)
  (e: enum key repr)
  (destr: enum_repr_of_key'_t e)
: Tot (l2r_leaf_writer u#0 (serialize_enum_key _ s e))
= [@inline_let] let _ = serialize_enum_key_synth_inverse e in
  l2r_leaf_write_synth
    (l2r_leaf_write_filter w (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    (serialize_enum_key_synth_recip e)
    (fun k -> destr k)

(* l2r_leaf_write_maybe_enum_key: write a maybe_enum_key using the repr writer *)
inline_for_extraction
let l2r_leaf_write_maybe_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (#s: serializer p)
  (w: l2r_leaf_writer u#0 s)
  (e: enum key repr)
  (destr: enum_repr_of_key'_t e)
: Tot (l2r_leaf_writer u#0 (serialize_maybe_enum_key _ s e))
= [@inline_let] let _ = serialize_enum_key_synth_inverse e in
  l2r_leaf_write_synth
    w
    (maybe_enum_key_of_repr e)
    (repr_of_maybe_enum_key e)
    (fun mk ->
      match mk with
      | Unknown r -> r
      | Known kk -> destr kk)

(* l2r_leaf_write_sum_cases_t: type of per-case writer for sum *)
inline_for_extraction
let l2r_leaf_write_sum_cases_t
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
: Tot Type
= l2r_leaf_writer u#0 (serialize_sum_cases t pc sc k)

inline_for_extraction
let l2r_leaf_write_sum_cases_t_eq
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
  (x y: l2r_leaf_write_sum_cases_t t sc k)
: GTot prop
= True

inline_for_extraction
fn l2r_leaf_write_sum_cases_t_if'
  (t: sum u#0 u#0)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (l2r_leaf_write_sum_cases_t t sc k)))
  (sv_false: (cond_false cond -> Tot (l2r_leaf_write_sum_cases_t t sc k)))
: l2r_leaf_write_sum_cases_t t sc k
=
    (x: t)
    (out: slice byte)
    (offset: SZ.t)
    (#v: _)
{
  if cond
  {
    sv_true () x out offset
  }
  else
  {
    sv_false () x out offset
  }
}

inline_for_extraction
let l2r_leaf_write_sum_cases_t_if
: (t: sum u#0 u#0) ->
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x)))) ->
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x))))) ->
  (k: sum_key t) ->
  Tot (if_combinator _ (l2r_leaf_write_sum_cases_t_eq t sc k))
= l2r_leaf_write_sum_cases_t_if'

inline_for_extraction
let l2r_leaf_write_sum_cases_aux
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (l2r_leaf_writer u#0 (sc x))))
  (k: sum_key t)
: Tot (l2r_leaf_writer u#0 (serialize_sum_cases t pc sc k))
= [@inline_let] let _ =
    Classical.forall_intro (parse_sum_cases_eq' t pc k);
    synth_sum_case_injective t k;
    synth_sum_case_inverse t k
  in
  l2r_leaf_write_synth
    (sc32 k)
    (synth_sum_case t k)
    (synth_sum_case_recip t k)
    (fun x -> synth_sum_case_recip t k x)

inline_for_extraction
let l2r_leaf_write_sum_cases
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (l2r_leaf_writer u#0 (sc x))))
  (destr: dep_enum_destr (sum_enum t) (l2r_leaf_write_sum_cases_t t sc))
  (k: sum_key t)
: Tot (l2r_leaf_writer u#0 (serialize_sum_cases t pc sc k))
= destr
    _
    (l2r_leaf_write_sum_cases_t_if t sc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (l2r_leaf_write_sum_cases_aux t sc sc32)
    k
