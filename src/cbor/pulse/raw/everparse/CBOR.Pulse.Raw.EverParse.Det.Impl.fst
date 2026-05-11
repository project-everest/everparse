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

module SpecRawBase = CBOR.Spec.Raw.Base
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

(* ======== Field readers ======== *)

module ReadFields = CBOR.Pulse.Raw.EverParse.ReadFields

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_read_simple_value (_: unit) : read_simple_value_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = ReadFields.cbor_raw_read_simple_value p x;
  fold (cbor_det_match p x v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_read_uint64 (_: unit) : read_uint64_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = ReadFields.cbor_raw_read_int64_value p x;
  fold (cbor_det_match p x v);
  res
}

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_get_string_length (_: unit) : get_string_length_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let s = Access.cbor_raw_get_string p x ();
  with pm' vs . assert (Pulse.Lib.Slice.pts_to s #pm' vs);
  Pulse.Lib.Slice.pts_to_len s;
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let len_sz = Pulse.Lib.Slice.len s;
  let res = SZ.sizet_to_uint64 len_sz;
  // We know vs == String?.v (mk_det_raw_cbor v)
  // and mk_cbor_eq tells us mk_cbor (mk_det_raw_cbor v) == v
  // so for CString ty content, mk_det_raw_cbor v = String ty _ content
  // hence vs == content and Seq.length vs == Seq.length content
  Trade.elim _ (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v));
  fold (cbor_det_match p x v);
  res
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_get_tagged_tag (_: unit) : get_tagged_tag_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = ReadFields.cbor_raw_read_tagged_tag p x;
  fold (cbor_det_match p x v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_get_array_length (_: unit) : get_array_length_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = ReadFields.cbor_raw_read_array_length p x;
  fold (cbor_det_match p x v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_get_map_length (_: unit) : get_map_length_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = ReadFields.cbor_raw_read_map_length p x;
  fold (cbor_det_match p x v);
  res
}

(* ======== Elim functions ======== *)

ghost
fn cbor_det_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  Access.cbor_raw_match_cases p x;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  drop_ (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v));
  drop_ (pure (Access.cbor_raw_match_cases_prop x (SpecRaw.mk_det_raw_cbor v)))
}

ghost
fn cbor_det_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  Access.cbor_raw_match_cases p x;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  drop_ (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor v));
  drop_ (pure (Access.cbor_raw_match_cases_prop x (SpecRaw.mk_det_raw_cbor v)))
}

(* ======== Reset perm ======== *)

module ResetPerm = CBOR.Pulse.Raw.EverParse.ResetPerm

ghost
fn cbor_det_reset_perm (_: unit) : reset_perm_t u#0 u#0 #_ #_ cbor_det_match
= (x: _)
  (#pm: _)
  (#v: _)
  (q: _)
{
  unfold (cbor_det_match pm x v);
  let x' = ResetPerm.cbor_raw_reset_perm pm x q;
  fold (cbor_det_match q x' v);
  Trade.intro_trade
    (cbor_det_match q x' v)
    (cbor_det_match pm x v)
    (Pulse.Lib.Trade.trade (RawMatch.cbor_raw_match q x' (SpecRaw.mk_det_raw_cbor v))
           (RawMatch.cbor_raw_match pm x (SpecRaw.mk_det_raw_cbor v)))
    fn _ {
      unfold (cbor_det_match q x' v);
      Trade.elim
        (RawMatch.cbor_raw_match q x' (SpecRaw.mk_det_raw_cbor v))
        (RawMatch.cbor_raw_match pm x (SpecRaw.mk_det_raw_cbor v));
      fold (cbor_det_match pm x v)
    };
  x'
}

(* ======== Constructors ======== *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_tagged (_: unit) : mk_tagged_t u#0 #_ cbor_det_match
= (tag: _)
  (r: _)
  (#pr: _)
  (#v: _)
  (#pv: _)
  (#v': _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let tag64 = SpecRaw.mk_raw_uint64 tag;
  let w' : Ghost.erased SpecRaw.raw_data_item = SpecRaw.mk_det_raw_cbor v';
  Trade.rewrite_with_trade
    (cbor_det_match pv v v')
    (RawMatch.cbor_raw_match pv v (Ghost.reveal w'));
  let res = RawMake.cbor_mk_tagged tag r;
  with r' . assert (RawMatch.cbor_raw_match 1.0R res r');
  Trade.trans_concl_r _ _ (RawMatch.cbor_raw_match pv v (Ghost.reveal w')) _;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v')));
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Tagged tag64 (Ghost.reveal w'));
  SpecRaw.mk_cbor_eq (SpecRaw.Tagged tag64 (Ghost.reveal w'));
  SpecRaw.mk_cbor_equiv (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v'))) (SpecRaw.Tagged tag64 (Ghost.reveal w'));
  SpecRaw.raw_equiv_sorted_optimal
    SpecF.deterministically_encoded_cbor_map_key_order
    (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v')))
    (SpecRaw.Tagged tag64 (Ghost.reveal w'));
  // Now we have r' == Tagged tag64 w' == mk_det_raw_cbor (pack (CTagged tag v'))
  // Rewrite r' everywhere (match + trade) before folding
  rewrite each r' as
    (SpecRaw.mk_det_raw_cbor (CBOR.Spec.API.Type.pack (CBOR.Spec.API.Type.CTagged tag v')));
  rewrite each (Ghost.reveal w') as (SpecRaw.mk_det_raw_cbor v');
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CTagged tag v')));
  // Trade now has cbor_raw_match 1.0R res (mk_det_raw_cbor (pack (CTagged tag v')))
  // which is cbor_det_match 1.0R res (pack (CTagged tag v'))
  // Also need to fold the trade postcondition
  Trade.intro_trade
    (cbor_det_match 1.0R res (Spec.pack (Spec.CTagged tag v')))
    (R.pts_to r #pr v ** cbor_det_match pv v v')
    (Pulse.Lib.Trade.trade
      (RawMatch.cbor_raw_match 1.0R res (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v'))))
      (R.pts_to r #pr v ** RawMatch.cbor_raw_match pv v (SpecRaw.mk_det_raw_cbor v')))
    fn _ {
      unfold (cbor_det_match 1.0R res (Spec.pack (Spec.CTagged tag v')));
      Trade.elim _ (R.pts_to r #pr v ** RawMatch.cbor_raw_match pv v (SpecRaw.mk_det_raw_cbor v'));
      fold (cbor_det_match pv v v')
    };
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_string (_: unit) : mk_string_t u#0 #_ cbor_det_match
= (ty: _)
  (s: _)
  (#p: _)
  (#v: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  Pulse.Lib.Slice.pts_to_len s;
  let len64 = SpecRaw.mk_raw_uint64 (SZ.sizet_to_uint64 (Pulse.Lib.Slice.len s));
  let res = RawMake.cbor_mk_string f64 ty s;
  with r . assert (RawMatch.cbor_raw_match 1.0R res r);
  // cbor_mk_string gives us all the pure postcondition facts
  let _p = elim_pure_explicit (
    CBOR.Spec.Raw.Optimal.raw_data_item_ints_optimal r /\
    CBOR.Spec.Raw.Sort.raw_data_item_sorted CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order r /\
    SpecRaw.valid_raw_data_item r /\
    SpecRaw.mk_det_raw_cbor (SpecRaw.mk_cbor r) == Ghost.reveal r /\
    SpecRaw.String? r /\
    SpecRaw.String?.typ r == ty /\
    (SpecRaw.String?.v r <: Seq.seq FStar.UInt8.t) == Ghost.reveal v
  );
  // With String? r, valid r, and mk_cbor_eq: mk_cbor r == pack (CString ty v)
  SpecRaw.mk_cbor_eq (Ghost.reveal r);
  // Rewrite r as mk_det_raw_cbor (mk_cbor r) and fold into cbor_det_match
  rewrite each r as (SpecRaw.mk_det_raw_cbor (SpecRaw.mk_cbor r));
  fold (cbor_det_match 1.0R res (SpecRaw.mk_cbor r));
  rewrite each (SpecRaw.mk_cbor r) as (Spec.pack (Spec.CString ty v));
  // Create the trade
  Trade.intro_trade
    (cbor_det_match 1.0R res (Spec.pack (Spec.CString ty v)))
    (Pulse.Lib.Slice.pts_to s #p v)
    (Pulse.Lib.Trade.trade
      (RawMatch.cbor_raw_match 1.0R res (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CString ty v))))
      (Pulse.Lib.Slice.pts_to s #p v))
    fn _ {
      unfold (cbor_det_match 1.0R res (Spec.pack (Spec.CString ty v)));
      Trade.elim _ (Pulse.Lib.Slice.pts_to s #p v)
    };
  res
}

#pop-options
