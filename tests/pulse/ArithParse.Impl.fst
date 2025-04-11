module ArithParse.Impl
#lang-pulse
include ArithParse.Spec
open LowParse.Spec.Base
open LowParse.Pulse.Base
open LowParse.Pulse.Combinators
open LowParse.Pulse.Int
open LowParse.Pulse.VCList
open LowParse.Pulse.Recursive
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Slice

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module PM = Pulse.Lib.SeqMatch

(* Validation *)

inline_for_extraction noextract [@@noextract_to "krml"]
let validate_header_rhs (lhs: U8.t) : validator (parse_header_rhs lhs) =
  ifthenelse_validator
    (parse_header_rhs lhs)
    (lhs = 255uy)
    (fun _ -> validate_weaken parse_header_rhs_kind (validate_u64))
    (fun _ -> validate_weaken parse_header_rhs_kind (validate_ret u_as_uint64))

inline_for_extraction noextract [@@noextract_to "krml"]
let validate_header : validator parse_header =
  validate_dtuple2 validate_u8 (leaf_reader_of_reader read_u8) validate_header_rhs

inline_for_extraction noextract [@@noextract_to "krml"]
let jump_header_rhs (lhs: U8.t) : jumper (parse_header_rhs lhs) =
  ifthenelse_jumper
    (parse_header_rhs lhs)
    (lhs = 255uy)
    (fun _ -> jump_ext (jump_u64) (parse_header_rhs lhs))
    (fun _ -> jump_ext (jump_ret u_as_uint64) (parse_header_rhs lhs))

inline_for_extraction noextract [@@noextract_to "krml"]
let jump_header : jumper parse_header =
  jump_dtuple2 jump_u8 (leaf_reader_of_reader read_u8) jump_header_rhs

inline_for_extraction noextract [@@noextract_to "krml"]
let read_header_rhs (lhs: U8.t) : reader (serialize_header_rhs lhs) =
  ifthenelse_reader
    (serialize_header_rhs lhs)
    (lhs = 255uy)
    (fun _ -> reader_ext (read_u64) (serialize_header_rhs lhs))
    (fun _ -> reader_ext (read_ret u_as_uint64 (fun _ -> ())) (serialize_header_rhs lhs))

let read_header () : leaf_reader #_ #_ #_ (serializer_of_tot_serializer tot_serialize_header) =
  [@@inline_let] let _ = parse_header_eq () in
  leaf_reader_of_reader
    (reader_ext (read_dtuple2 jump_u8 read_u8 read_header_rhs) _)

module SZ = FStar.SizeT

#push-options "--ifuel 4"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_validate_count_payload () : validate_recursive_step_count #_ serialize_expr_param =
  (#va: _)
  (#pm: _)
  (a: _)
  (bound: _)
  (#rem: _)
  (prem: _)
{
  let h = read_header () a;
  let Mkdtuple2 kd len = h;
  if (kd = 255uy) {
    prem := 0sz;
    false
  }
  else if (kd = 254uy) {
    prem := 2sz;
    false
  } else {
    let len16 = FStar.Int.Cast.uint8_to_uint16 kd;
    prem := SZ.uint16_to_sizet len16;
    false
  }
}

let validate_expr : validator tot_parse_expr =
  [@@inline_let] let _ = parse_header_eq () in
  validate_recursive serialize_expr_param validate_header (impl_validate_count_payload ())

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_jump_count_payload () : jump_recursive_step_count #_ serialize_expr_param =
  (#va: _)
  (#pm: _)
  (a: _)
  (bound: _)
{
  let h = read_header () a;
  let Mkdtuple2 kd len = h;
  if (kd = 255uy) {
    0sz;
  }
  else if (kd = 254uy) {
    2sz;
  } else {
    let len16 = FStar.Int.Cast.uint8_to_uint16 kd;
    SZ.uint16_to_sizet len16;
  }
}

let jump_expr : jumper tot_parse_expr =
  [@@inline_let] let _ = parse_header_eq () in
  jump_recursive serialize_expr_param jump_header (impl_jump_count_payload ())

(* Low-level data structure *)

noeq
type expr_t =
| EUnparsed of with_perm (S.slice U8.t)
| EPlus of with_perm (S.slice expr_t)
| EMinus of (with_perm (ref expr_t) & with_perm (ref expr_t))
| EValue of U64.t

(* Separation-logic predicate *)

let nlist_match_slice0
  (#telem: Type0)
  (#t: Type)
  (vmatch: (telem -> t -> slprop))
= nlist_match_slice Some (fun _ -> vmatch)

let nlist_match_slice_wf
  (#telem: Type0)
  (#t: Type)
  (n: nat)
  (a: _)
  (l: LowParse.Spec.VCList.nlist n t)
  (vmatch: (telem -> (x: t { x << l }) -> slprop))
: Tot slprop
= exists* (ar: with_perm (S.slice telem)) c .
    pts_to ar.v #ar.p c **
    PM.seq_list_match c l (vmatch) **
    pure (Some a == Some ar)

let nlist_match_slice_wf_eq
  (#telem: Type0)
  (#t: Type)
  (vmatch: (telem -> t -> slprop))
  (n: nat)
  (a: _)
  (l: LowParse.Spec.VCList.nlist n t)
: Lemma
  (nlist_match_slice0 vmatch n a l == nlist_match_slice_wf n a l vmatch)
= assert_norm (nlist_match_slice0 vmatch n a l == nlist_match_slice_wf n a l vmatch)

let vmatch_pair
  (#tl1 #tl2 #th1 #th2: Type)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: tl2 -> th2 -> slprop)
  (xl: (tl1 & tl2))
  (xh: (th1 & th2))
: Tot slprop
= vmatch1 (fst xl) (fst xh) ** vmatch2 (snd xl) (snd xh)

let vmatch_ref
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
: Tot slprop
= exists* vl . pts_to r.v #r.p vl ** vmatch vl vh

let vmatch_ref_wf0
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> (vh: th { vh << bound }) -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
  (sq: option (squash (vh << bound)))
: Tot slprop
= match sq with
  | Some _ -> exists* vl . pts_to r.v #r.p vl ** vmatch vl vh
  | None -> pure False

let vmatch_ref_wf
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> (vh: th { vh << bound }) -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
: Tot slprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (vh << bound)
  then vmatch_ref_wf0 bound vmatch r vh (Some ())
  else pure False

let vmatch_ref_wf_eq
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> th -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
: Lemma
  (requires (vh << bound))
  (ensures (vmatch_ref_wf bound vmatch r vh == vmatch_ref vmatch r vh))
= let b = (FStar.StrongExcludedMiddle.strong_excluded_middle (vh << bound)) in // FIXME: WHY WHY WHY the let binding?
  assert (vmatch_ref_wf bound vmatch r vh == vmatch_ref_wf0 bound vmatch r vh (Some ()));
  assert_norm (vmatch_ref_wf0 bound vmatch r vh (Some ()) == vmatch_ref vmatch r vh)

let rec rel
  (low: expr_t)
  (high: expr)
: Tot slprop
  (decreases high)
= match low, high with
  | EUnparsed s, _ -> pts_to_serialized_with_perm (serializer_of_tot_serializer tot_serialize_expr) s high
  | EPlus s, Plus l -> nlist_match_slice_wf (List.Tot.length l) s l rel
  | EMinus pl, Minus ph -> vmatch_pair (vmatch_ref_wf (Minus ph) rel) (vmatch_ref_wf (Minus ph) rel) pl ph
  | EValue vl, Value vh -> eq_as_slprop U64.t vl vh
  | _ -> pure False

let rel'
  (low: expr_t)
  (high: expr)
: Tot slprop
  (decreases high)
= match low, high with
  | EPlus s, Plus l -> nlist_match_slice0 rel (List.Tot.length l) s l
  | EMinus pl, Minus ph -> vmatch_pair (vmatch_ref rel) (vmatch_ref rel) pl ph
  | EValue vl, Value vh -> eq_as_slprop U64.t vl vh
  | EUnparsed s, _ -> pts_to_serialized_with_perm (serializer_of_tot_serializer tot_serialize_expr) s high
  | _ -> pure False

let rel_eq
  (low: expr_t)
  (high: expr)
: Lemma
  (rel low high == rel' low high)
= match low, high with
  | EPlus s, Plus l ->
    assert_norm (rel (EPlus s) (Plus l) == nlist_match_slice_wf (List.Tot.length l) s l (rel));
    assert_norm (rel' (EPlus s) (Plus l) == nlist_match_slice0 rel (List.Tot.length l) s l);
    nlist_match_slice_wf_eq (rel) (List.Tot.length l) s l;
    ()
  | EMinus pl, Minus ph ->
    assert (rel (EMinus pl) (Minus ph) == vmatch_pair (vmatch_ref_wf (Minus ph) rel) (vmatch_ref_wf (Minus ph) rel) pl ph) by (FStar.Tactics.trefl ());
    assert (rel' (EMinus pl) (Minus ph) == vmatch_pair (vmatch_ref rel) (vmatch_ref rel) pl ph) by (FStar.Tactics.trefl ());
    vmatch_ref_wf_eq (Minus ph) rel (fst pl) (fst ph);
    vmatch_ref_wf_eq (Minus ph) rel (snd pl) (snd ph);
    ()
  | _ -> ()

// from now on, rel should be opaque

let rel_cases_bool
  (low: expr_t)
  (high: expr)
: GTot bool
  (decreases high)
= match low, high with
  | EPlus _, Plus _
  | EMinus _, Minus _
  | EValue _, Value _
  | EUnparsed _, _ -> true
  | _ -> false

ghost fn rel_cases
  (low: expr_t)
  (high: expr)
requires rel low high
ensures rel low high ** pure (rel_cases_bool low high == true)
{
  let g = rel_cases_bool low high;
  if (g) {
    ()
  } else {
    rewrite (rel low high) as (pure False);
    rewrite (pure False) as (rel low high)
  }
}
