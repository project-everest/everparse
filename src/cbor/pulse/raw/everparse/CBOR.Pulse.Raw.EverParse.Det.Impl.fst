module CBOR.Pulse.Raw.EverParse.Det.Impl
#lang-pulse
friend CBOR.Pulse.API.Det.Type
friend CBOR.Spec.API.Format

open Pulse.Lib.Pervasives
open CBOR.Spec.Constants
open CBOR.Pulse.API.Base

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SU = Pulse.Lib.Slice.Util
module AP = Pulse.Lib.ArrayPtr

module SpecRaw = CBOR.Spec.Raw
module RawType = CBOR.Pulse.Raw.EverParse.Type
module RawMatch = CBOR.Pulse.Raw.EverParse.Match
module Access = CBOR.Pulse.Raw.EverParse.Access
module RawMake = CBOR.Pulse.Raw.EverParse.Make
module RawSerialize = CBOR.Pulse.Raw.EverParse.Serialize
module Compare = CBOR.Pulse.Raw.EverParse.Det.Compare
module SpecF = CBOR.Spec.Raw.Format
module I = LowParse.PulseParse.Iterator
module R = Pulse.Lib.Reference

(* ======== Core definition ======== *)

[@@pulse_unfold]
let cbor_det_match p c v =
  RawMatch.cbor_raw_match p c (SpecRaw.mk_det_raw_cbor v)

(* Local type aliases for types that reference our cbor_det_match *)

inline_for_extraction noextract [@@noextract_to "krml"]
let det_get_string_t =
  (x: cbor_det_t) ->
  (#p: perm) ->
  (#y: Ghost.erased Spec.cbor) ->
  stt (AP.ptr U8.t)
    (cbor_det_match p x y ** pure (Spec.CString? (Spec.unpack y)))
    (fun res -> exists* p' v' .
      pts_to res #p' v' **
      Trade.trade
        (pts_to res #p' v')
        (cbor_det_match p x y) **
      pure (get_string_post y v')
    )

inline_for_extraction noextract [@@noextract_to "krml"]
let det_impl_utf8_correct_from_array_t =
  (s: AP.ptr U8.t) ->
  (len: SZ.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v ** pure (SZ.v len == Seq.length v))
    (fun res -> pts_to s #p v ** pure (res == CBOR.Spec.API.UTF8.correct v))

(* ======== Share / Gather ======== *)

ghost
fn cbor_det_share (_: unit)
: share_t u#0 u#0 #_ #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  RawMatch.cbor_raw_match_share x;
  fold (cbor_det_match (p /. 2.0R) x v);
  fold (cbor_det_match (p /. 2.0R) x v);
}

ghost
fn cbor_det_gather (_: unit)
: gather_t u#0 u#0 #_ #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
  (#p': _)
  (#v': _)
{
  unfold (cbor_det_match p x v);
  unfold (cbor_det_match p' x v');
  RawMatch.cbor_raw_match_gather x #p #(SpecRaw.mk_det_raw_cbor v) #p' #(SpecRaw.mk_det_raw_cbor v');
  SpecRaw.mk_det_raw_cbor_inj v v';
  fold (cbor_det_match (p +. p') x v);
}

(* reset_perm requires internal struct manipulation — TODO *)

(* ======== Size ======== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_size
  (x: cbor_det_t)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (cbor_det_match pm x y)
returns res: SZ.t
ensures
    (cbor_det_match pm x y ** pure (
      cbor_det_size_post bound y res
    ))
{
  unfold (cbor_det_match pm x y);
  let res = RawSerialize.cbor_size (assume (SZ.fits_u64)) x bound;
  fold (cbor_det_match pm x y);
  res
}

(* ======== Equal ======== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_equal (_: unit) : equal_t u#0 #_ cbor_det_match
= (x1: _)
  (x2: _)
  (#p1: _)
  (#p2: _)
  (#v1: _)
  (#v2: _)
{
  Classical.move_requires (SpecRaw.mk_det_raw_cbor_inj v1) v2;
  SpecF.cbor_compare_equal (SpecRaw.mk_det_raw_cbor v1) (SpecRaw.mk_det_raw_cbor v2);
  unfold (cbor_det_match p1 x1 v1);
  unfold (cbor_det_match p2 x2 v2);
  let comp = Compare.impl_cbor_compare (assume (SZ.fits_u64)) x1 x2;
  fold (cbor_det_match p1 x1 v1);
  fold (cbor_det_match p2 x2 v2);
  (comp = 0s)
}

(* ======== Major type ======== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_major_type (_: unit) : get_major_type_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Access.cbor_raw_get_major_type p x;
  fold (cbor_det_match p x v);
  res
}

(* ======== Tagged ======== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_get_tagged_payload (_: unit) : get_tagged_payload_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  Trade.rewrite_with_trade
    (cbor_det_match p x v)
    (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v));
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Access.cbor_raw_get_tagged_payload p x (assume (SZ.fits_u64)) ();
  Trade.trans _ (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v)) (cbor_det_match p x v);
  with p' v' . assert (RawMatch.cbor_raw_match p' res v');
  SpecRaw.mk_det_raw_cbor_mk_cbor v';
  Trade.rewrite_with_trade
    (RawMatch.cbor_raw_match p' res v')
    (cbor_det_match p' res (SpecRaw.mk_cbor v'));
  Trade.trans _ _ (cbor_det_match p x v);
  res
}

(* ======== String accessor ======== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_get_string (_: unit) : det_get_string_t
= (x: _)
  (#p: _)
  (#v: _)
{
  Trade.rewrite_with_trade
    (cbor_det_match p x v)
    (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v));
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let s = Access.cbor_raw_get_string p x ();
  Trade.trans _ (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v)) (cbor_det_match p x v);
  with pm' vs . assert (S.pts_to s #pm' vs);
  let res = SU.slice_to_arrayptr_intro_trade s;
  Trade.trans _ _ (cbor_det_match p x v);
  res
}

(* ======== Constructors ======== *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_simple_value (_: unit) : mk_simple_t u#0 #_ cbor_det_match
= (v: _)
{
  let res = RawMake.cbor_mk_simple_value v;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CSimple v)));
  rewrite RawMatch.cbor_raw_match 1.0R res (SpecRaw.Simple v) as
    RawMatch.cbor_raw_match 1.0R res (SpecRaw.mk_det_raw_cbor (CBOR.Spec.API.Type.pack (CBOR.Spec.API.Type.CSimple v)));
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CSimple v)));
  res
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_int64 (_: unit) : mk_int64_t u#0 #_ cbor_det_match
= (ty: _)
  (v: _)
{
  let res = RawMake.cbor_mk_int64 ty v;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CInt64 ty v)));
  rewrite RawMatch.cbor_raw_match 1.0R res (SpecRaw.Int64 ty (SpecRaw.mk_raw_uint64 v)) as
    RawMatch.cbor_raw_match 1.0R res (SpecRaw.mk_det_raw_cbor (CBOR.Spec.API.Type.pack (CBOR.Spec.API.Type.CInt64 ty v)));
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CInt64 ty v)));
  res
}

#pop-options

(* ======== Serialize ======== *)

fn cbor_det_serialize
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      SZ.v output_len == Seq.length v /\
      cbor_det_serialize_fits_postcond y res v
    ))
{
  unfold (cbor_det_match pm x y);
  assert (pure (Spec.cbor_det_serialize y == SpecF.serialize_cbor (SpecRaw.mk_det_raw_cbor y)));
  let s = S.arrayptr_to_slice_intro output output_len;
  S.pts_to_len s;
  let res = RawSerialize.cbor_serialize (assume (SZ.fits_u64)) x s;
  S.pts_to_len s;
  S.arrayptr_to_slice_elim s;
  fold (cbor_det_match pm x y);
  res
}

fn cbor_det_serialize_safe
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
requires
    (cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      SZ.v output_len == Seq.length v' /\
      cbor_det_serialize_postcond_c y v v' res
    ))
{
  unfold (cbor_det_match pm x y);
  assert (pure (Spec.cbor_det_serialize y == SpecF.serialize_cbor (SpecRaw.mk_det_raw_cbor y)));
  let s = S.arrayptr_to_slice_intro output output_len;
  S.pts_to_len s;
  // Get the serialized size
  let sz = RawSerialize.cbor_size (assume (SZ.fits_u64)) x output_len;
  // sz > 0 because serialize fits within output_len (from precondition)
  // Split the slice at sz: first sz bytes for serialize, rest untouched
  let pair = S.split s sz;
  S.pts_to_len (fst pair);
  // Serialize to first part only — tail is untouched
  let res = RawSerialize.cbor_serialize (assume (SZ.fits_u64)) x (fst pair);
  // After serialize: fst pair has new content v_new
  S.pts_to_len (fst pair);
  with v_new . assert (S.pts_to (fst pair) v_new);
  // v_new == Spec.cbor_det_serialize y (from length + prefix constraint)
  Seq.lemma_eq_elim v_new (SpecF.serialize_cbor (SpecRaw.mk_det_raw_cbor y));
  // Join back into s
  S.join (fst pair) (snd pair) s;
  // Help the solver with Seq.slice equalities for the postcondition
  Seq.append_slices (Spec.cbor_det_serialize y) (Seq.slice v (SZ.v sz) (Seq.length v));
  assert (pure (SZ.v res <> 0));
  S.pts_to_len s;
  S.arrayptr_to_slice_elim s;
  fold (cbor_det_match pm x y);
  res
}

(* ======== UTF8 ======== *)

fn cbor_det_impl_utf8_correct_from_array (_: unit) : det_impl_utf8_correct_from_array_t
= (s: _)
  (len: _)
  (#p: _)
  (#v: _)
{
  let sl = SU.arrayptr_to_slice_intro_trade s len;
  let res = CBOR.Pulse.API.UTF8.impl_utf8_correct sl;
  Trade.elim _ (pts_to s #p v);
  res
}

(* TODO: remaining functions need additional infrastructure:
   - read_simple_value, read_uint64, get_string_length, get_tagged_tag,
     get_array_length, get_map_length: need header extraction helpers
   - elim_simple, elim_int64: need match elimination helpers
   - validate, parse: need cbor_validate_det, cbor_raw_parse_det
   - mk_tagged, mk_string, mk_array, mk_map: need Make module wrappers
   - iterators: need iterator bridge infrastructure
   - map_get: needs comparison + iterator infrastructure
   - serialize_*_to_array: need Serialize module wrappers
*)
