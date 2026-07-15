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

(* ===== Pure structural [leaf_size] analogs of the leaf writers above ===== *)

(* leaf_size_sum_cases_t: type of per-case size for sum *)
inline_for_extraction
let leaf_size_sum_cases_t
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
: Tot Type
= leaf_size (serialize_sum_cases t pc sc k)

inline_for_extraction
let leaf_size_sum_cases_t_eq
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
  (x y: leaf_size_sum_cases_t t sc k)
: GTot prop
= True

inline_for_extraction
let leaf_size_sum_cases_t_if'
  (t: sum u#0 u#0)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (leaf_size_sum_cases_t t sc k)))
  (sv_false: (cond_false cond -> Tot (leaf_size_sum_cases_t t sc k)))
: leaf_size_sum_cases_t t sc k
= fun x -> if cond then sv_true () x else sv_false () x

inline_for_extraction
let leaf_size_sum_cases_t_if
: (t: sum u#0 u#0) ->
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x)))) ->
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x))))) ->
  (k: sum_key t) ->
  Tot (if_combinator _ (leaf_size_sum_cases_t_eq t sc k))
= leaf_size_sum_cases_t_if'

inline_for_extraction
let leaf_size_sum_cases_aux
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (leaf_size (sc x))))
  (k: sum_key t)
: Tot (leaf_size (serialize_sum_cases t pc sc k))
= fun x ->
  [@inline_let] let _ =
    Classical.forall_intro (parse_sum_cases_eq' t pc k);
    synth_sum_case_injective t k;
    synth_sum_case_inverse t k
  in
  leaf_size_synth
    (sc32 k)
    (synth_sum_case t k)
    (synth_sum_case_recip t k)
    (fun x -> synth_sum_case_recip t k x)
    x

inline_for_extraction
let leaf_size_sum_cases
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (leaf_size (sc x))))
  (destr: dep_enum_destr (sum_enum t) (leaf_size_sum_cases_t t sc))
  (k: sum_key t)
: Tot (leaf_size (serialize_sum_cases t pc sc k))
= destr
    _
    (leaf_size_sum_cases_t_if t sc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (leaf_size_sum_cases_aux t sc sc32)
    k

(* leaf_size_dsum chains *)

inline_for_extraction
let leaf_size_dsum_type_of_tag
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (leaf_size (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: leaf_size sg) (tg: dsum_key t)
: Tot (leaf_size (serialize_dsum_type_of_tag t f sf g sg tg))
= fun x ->
  match tg with
  | Known x' ->
    serializer_unique_strong (sf x') (serialize_dsum_type_of_tag t f sf g sg tg) x;
    sf32 x' x
  | Unknown x' ->
    serializer_unique_strong sg (serialize_dsum_type_of_tag t f sf g sg tg) x;
    sg32 x

inline_for_extraction
let leaf_size_dsum_cases_aux
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (leaf_size (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: leaf_size sg) (tg: dsum_key t)
: Tot (leaf_size (serialize_dsum_cases t f sf g sg tg))
= fun x ->
  [@inline_let] let _ = synth_dsum_case_injective t tg in
  [@inline_let] let _ = synth_dsum_case_inverse t tg in
  [@inline_let] let _ =
    serialize_synth_eq
      (parse_dsum_type_of_tag t f g tg)
      (synth_dsum_case t tg)
      (serialize_dsum_type_of_tag t f sf g sg tg)
      (synth_dsum_case_recip t tg)
      ()
      x
  in
  leaf_size_dsum_type_of_tag t f sf sf32 sg32 tg (synth_dsum_case_recip t tg x)

inline_for_extraction
let leaf_size_dsum_cases_t
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (k: dsum_known_key t) : Tot Type
= leaf_size (serialize_dsum_cases t f sf g sg (Known k))

inline_for_extraction
let leaf_size_dsum_cases_t_if'
  (t: dsum u#0 u#0) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (k: dsum_known_key t)
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (leaf_size_dsum_cases_t t f sf g sg k)))
  (sv_false: (cond_false cond -> Tot (leaf_size_dsum_cases_t t f sf g sg k)))
: leaf_size_dsum_cases_t t f sf g sg k
= fun x -> if cond then sv_true () x else sv_false () x

inline_for_extraction
let leaf_size_dsum_cases_t_if
: (t: dsum) -> (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))) ->
  (sf: ((x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))) ->
  (#k': Ghost.erased parser_kind) -> (g: parser k' (dsum_type_of_unknown_tag t)) -> (sg: serializer g) ->
  (k: dsum_known_key t) ->
  Tot (if_combinator _ (fun (x y: leaf_size_dsum_cases_t t f sf g sg k) -> True))
= leaf_size_dsum_cases_t_if'

inline_for_extraction
let leaf_size_dsum_cases_known
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (leaf_size (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: leaf_size sg)
  (destr: dep_enum_destr _ (leaf_size_dsum_cases_t t f sf g sg))
  (k: dsum_known_key t)
: (leaf_size (serialize_dsum_cases t f sf g sg (Known k)))
= destr _ (leaf_size_dsum_cases_t_if t f sf g sg) (fun _ _ -> ()) (fun _ _ _ _ -> ())
      (fun k -> leaf_size_dsum_cases_aux t f sf sf32 sg32 (Known k)) k

inline_for_extraction
let leaf_size_dsum_cases
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (leaf_size (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: leaf_size sg)
  (destr: dep_enum_destr _ (leaf_size_dsum_cases_t t f sf g sg)) (tg: dsum_key t)
: (leaf_size (serialize_dsum_cases t f sf g sg tg))
= match tg with
  | Known k -> leaf_size_dsum_cases_known t f sf sf32 sg32 destr k
  | Unknown r -> leaf_size_dsum_cases_aux t f sf sf32 sg32 (Unknown r)
