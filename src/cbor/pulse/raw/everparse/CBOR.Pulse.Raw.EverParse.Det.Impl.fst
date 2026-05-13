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
module ResetPerm = CBOR.Pulse.Raw.EverParse.ResetPerm
module SpecF = CBOR.Spec.Raw.Format
module I = LowParse.PulseParse.Iterator
module R = Pulse.Lib.Reference
module Proj = LowParse.PulseParse.Projectors

(* ======== Core definition ======== *)

[@@pulse_unfold]
let cbor_det_match p c v =
  RawMatch.cbor_raw_match p c (SpecRaw.mk_det_raw_cbor v)

(* Local type aliases for types that reference our cbor_det_match — exposed in fsti *)

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

(* ======== Map entries ======== *)

[@@pulse_unfold]
let cbor_det_map_entry_match
  (pm: perm)
  (entry: CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t)
  (pair: Spec.cbor & Spec.cbor)
: Tot slprop
= RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm entry
    (SpecRaw.mk_det_raw_cbor (fst pair), SpecRaw.mk_det_raw_cbor (snd pair))

(* ---- map entry share/gather ---- *)

ghost
fn cbor_det_map_entry_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_det_map_entry_match
= (e: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_det_map_entry_match p e v2);
  ghost
  fn p_share_local (x1: RawType.cbor_raw) (#pm0: perm) (#x2: SpecRawBase.raw_data_item)
  requires RawMatch.cbor_raw_match pm0 x1 x2
  ensures RawMatch.cbor_raw_match (pm0 /. 2.0R) x1 x2 ** RawMatch.cbor_raw_match (pm0 /. 2.0R) x1 x2
  {
    RawMatch.cbor_raw_match_share x1 #pm0 #x2
  };
  RawMatch.cbor_map_entry_match_share RawMatch.cbor_raw_match
    p_share_local
    e;
  fold (cbor_det_map_entry_match (p /. 2.0R) e v2);
  fold (cbor_det_map_entry_match (p /. 2.0R) e v2);
}

ghost
fn cbor_det_map_entry_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_det_map_entry_match
= (e: _)
  (#p: _)
  (#v2: _)
  (#p': _)
  (#v2': _)
{
  unfold (cbor_det_map_entry_match p e v2);
  unfold (cbor_det_map_entry_match p' e v2');
  ghost
  fn p_gather_local
    (x1: RawType.cbor_raw)
    (#pm0: perm)
    (#x2: SpecRawBase.raw_data_item)
    (#pm0': perm)
    (x2': SpecRawBase.raw_data_item { x2' << (SpecRaw.mk_det_raw_cbor (fst v2'), SpecRaw.mk_det_raw_cbor (snd v2')) })
  requires RawMatch.cbor_raw_match pm0 x1 x2 ** RawMatch.cbor_raw_match pm0' x1 x2'
  ensures RawMatch.cbor_raw_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
  {
    RawMatch.cbor_raw_match_gather x1 #pm0 #x2 #pm0' #x2'
  };
  RawMatch.cbor_map_entry_match_gather RawMatch.cbor_raw_match e
    #p
    #(SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2))
    #p'
    #(SpecRaw.mk_det_raw_cbor (fst v2'), SpecRaw.mk_det_raw_cbor (snd v2'))
    p_gather_local;
  SpecRaw.mk_det_raw_cbor_inj (fst v2) (fst v2');
  SpecRaw.mk_det_raw_cbor_inj (snd v2) (snd v2');
  fold (cbor_det_map_entry_match (p +. p') e v2);
}

(* ======== Map entry key/value ======== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_det_map_entry_match cbor_det_match
= (e: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_det_map_entry_match p e v2);
  unfold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e
    (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
  unfold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
    (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
    e (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
  unfold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
    e (SpecRaw.mk_det_raw_cbor (snd v2)));
  rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (fst v2)))
       as (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key (SpecRaw.mk_det_raw_cbor (fst v2)));
  rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (snd v2)))
       as (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value (SpecRaw.mk_det_raw_cbor (snd v2)));
  fold (cbor_det_match p e.RawType.cbor_map_entry_key (fst v2));
  Trade.intro_trade
    (cbor_det_match p e.RawType.cbor_map_entry_key (fst v2))
    (cbor_det_map_entry_match p e v2)
    (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value (SpecRaw.mk_det_raw_cbor (snd v2)))
    fn _ {
      unfold (cbor_det_match p e.RawType.cbor_map_entry_key (fst v2));
      rewrite (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key (SpecRaw.mk_det_raw_cbor (fst v2)))
           as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (fst v2)));
      rewrite (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value (SpecRaw.mk_det_raw_cbor (snd v2)))
           as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
        e (SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
        e (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e
        (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (cbor_det_map_entry_match p e v2);
    };
  e.RawType.cbor_map_entry_key
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_det_map_entry_match cbor_det_match
= (e: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_det_map_entry_match p e v2);
  unfold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e
    (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
  unfold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
    (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
    e (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
  unfold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
    e (SpecRaw.mk_det_raw_cbor (snd v2)));
  rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (fst v2)))
       as (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key (SpecRaw.mk_det_raw_cbor (fst v2)));
  rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (snd v2)))
       as (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value (SpecRaw.mk_det_raw_cbor (snd v2)));
  fold (cbor_det_match p e.RawType.cbor_map_entry_value (snd v2));
  Trade.intro_trade
    (cbor_det_match p e.RawType.cbor_map_entry_value (snd v2))
    (cbor_det_map_entry_match p e v2)
    (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key (SpecRaw.mk_det_raw_cbor (fst v2)))
    fn _ {
      unfold (cbor_det_match p e.RawType.cbor_map_entry_value (snd v2));
      rewrite (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key (SpecRaw.mk_det_raw_cbor (fst v2)))
           as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (fst v2)));
      rewrite (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value (SpecRaw.mk_det_raw_cbor (snd v2)))
           as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get e) (SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
        e (SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
        e (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e
        (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
      fold (cbor_det_map_entry_match p e v2);
    };
  e.RawType.cbor_map_entry_value
}

#pop-options

(* ======== mk_map_entry ======== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_map_entry (_: unit) : mk_map_entry_t u#0 u#0 #_ #_ cbor_det_match cbor_det_map_entry_match
= (xk: _) (xv: _) (#pk: _) (#vk: _) (#pv: _) (#vv: _)
{
  unfold (cbor_det_match pk xk vk);
  let xk' = ResetPerm.cbor_raw_reset_perm pk xk 1.0R;
  // T1 : RawMatch pk xk (det vk) <== RawMatch 1.0R xk' (det vk)
  unfold (cbor_det_match pv xv vv);
  let xv' = ResetPerm.cbor_raw_reset_perm pv xv 1.0R;
  // T2 : RawMatch pv xv (det vv) <== RawMatch 1.0R xv' (det vv)
  let res = RawMake.cbor_mk_map_entry xk' xv'
    #1.0R
    #(SpecRaw.mk_det_raw_cbor vk)
    #(SpecRaw.mk_det_raw_cbor vv);
  // T3 : cbor_map_entry_match RawMatch 1.0R res (det vk, det vv) ==>
  //      (RawMatch 1.0R xk' (det vk) ** RawMatch 1.0R xv' (det vv))
  // Replace right half (xv' -> xv at perm pv) using T2 via trans_concl_r
  Trade.trans_concl_r _ _ _ (RawMatch.cbor_raw_match pv xv (SpecRaw.mk_det_raw_cbor vv));
  // Replace left half (xk' -> xk at perm pk) using T1 via trans_concl_l
  Trade.trans_concl_l _ _ (RawMatch.cbor_raw_match pk xk (SpecRaw.mk_det_raw_cbor vk)) _;
  fold (cbor_det_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv));
  // Wrap the right-hand side of the trade with cbor_det_match folds
  Trade.intro_trade
    (cbor_det_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv))
    (cbor_det_match pk xk vk ** cbor_det_match pv xv vv)
    (Pulse.Lib.Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match 1.0R res
        (SpecRaw.mk_det_raw_cbor vk, SpecRaw.mk_det_raw_cbor vv))
      (RawMatch.cbor_raw_match pk xk (SpecRaw.mk_det_raw_cbor vk) **
       RawMatch.cbor_raw_match pv xv (SpecRaw.mk_det_raw_cbor vv)))
    fn _ {
      unfold (cbor_det_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv));
      Trade.elim
        (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match 1.0R res
          (SpecRaw.mk_det_raw_cbor vk, SpecRaw.mk_det_raw_cbor vv))
        (RawMatch.cbor_raw_match pk xk (SpecRaw.mk_det_raw_cbor vk) **
         RawMatch.cbor_raw_match pv xv (SpecRaw.mk_det_raw_cbor vv));
      fold (cbor_det_match pk xk vk);
      fold (cbor_det_match pv xv vv);
    };
  res
}

#pop-options

(* ======== Array iterator ======== *)

module SpecRawEverParse = CBOR.Spec.Raw.EverParse
module Validate = CBOR.Pulse.Raw.EverParse.Validate
module Aux = CBOR.Pulse.Raw.EverParse.Det.Impl.Aux

[@@pulse_unfold]
let cbor_det_array_iterator_match
  (pm: perm)
  (it: CBOR.Pulse.API.Det.Type.cbor_det_array_iterator_t)
  (l: list Spec.cbor)
: Tot slprop
= I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it
    (Aux.det_raw_list l) **
  pure (FStar.UInt.fits (List.Tot.length l) U64.n)

ghost
fn cbor_raw_match_share_aux (x1: RawType.cbor_raw) (#pm0: perm) (#x2: SpecRawBase.raw_data_item)
  requires RawMatch.cbor_raw_match pm0 x1 x2
  ensures RawMatch.cbor_raw_match (pm0 /. 2.0R) x1 x2 ** RawMatch.cbor_raw_match (pm0 /. 2.0R) x1 x2
{
  RawMatch.cbor_raw_match_share x1 #pm0 #x2
}

ghost
fn cbor_raw_match_gather_aux
    (x1: RawType.cbor_raw)
    (#pm0: perm)
    (#x2: SpecRawBase.raw_data_item)
    (#pm0': perm)
    (#x2': SpecRawBase.raw_data_item)
  requires RawMatch.cbor_raw_match pm0 x1 x2 ** RawMatch.cbor_raw_match pm0' x1 x2'
  ensures RawMatch.cbor_raw_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
{
  RawMatch.cbor_raw_match_gather x1 #pm0 #x2 #pm0' #x2'
}

ghost
fn cbor_det_array_iterator_share (_: unit) : share_t cbor_det_array_iterator_match
= (it: _) (#pm: _) (#l: _)
{
  let lr = Ghost.hide (Aux.det_raw_list l);
  unfold (cbor_det_array_iterator_match pm it l);
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it
    (Aux.det_raw_list l))
    as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it
    (Ghost.reveal lr));
  unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it
    (Ghost.reveal lr));
  with l1 l2 . assert (
    I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it.LowParse.PulseParse.Iterator.after l2);
  I.base_mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it.LowParse.PulseParse.Iterator.before l1 cbor_raw_match_share_aux;
  I.mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it.LowParse.PulseParse.Iterator.after l2 cbor_raw_match_share_aux;
  fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm /. 2.0R) it
    (Ghost.reveal lr));
  fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm /. 2.0R) it
    (Ghost.reveal lr));
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm /. 2.0R) it
    (Ghost.reveal lr))
    as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm /. 2.0R) it
    (Aux.det_raw_list l));
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm /. 2.0R) it
    (Ghost.reveal lr))
    as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm /. 2.0R) it
    (Aux.det_raw_list l));
  fold (cbor_det_array_iterator_match (pm /. 2.0R) it l);
  fold (cbor_det_array_iterator_match (pm /. 2.0R) it l);
}

ghost
fn cbor_det_array_iterator_gather (_: unit) : gather_t cbor_det_array_iterator_match
= (it: _) (#pm: _) (#l: _) (#pm': _) (#l': _)
{
  let lr  = Ghost.hide (Aux.det_raw_list l);
  let lr' = Ghost.hide (Aux.det_raw_list l');
  unfold (cbor_det_array_iterator_match pm it l);
  unfold (cbor_det_array_iterator_match pm' it l');
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it (Aux.det_raw_list l))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it (Ghost.reveal lr));
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it (Aux.det_raw_list l'))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it (Ghost.reveal lr'));
  unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it (Ghost.reveal lr));
  unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it (Ghost.reveal lr'));
  with l1 l2 . assert (
    I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it.LowParse.PulseParse.Iterator.after l2);
  with l1' l2' . assert (
    I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it.LowParse.PulseParse.Iterator.before l1' **
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it.LowParse.PulseParse.Iterator.after l2');
  I.base_mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm pm' it.LowParse.PulseParse.Iterator.before l1 l1' cbor_raw_match_gather_aux;
  I.mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm pm' it.LowParse.PulseParse.Iterator.after l2 l2' cbor_raw_match_gather_aux;
  List.Tot.append_injective l1 l1' l2 l2';
  fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm +. pm') it (Ghost.reveal lr));
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm +. pm') it (Ghost.reveal lr))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (pm +. pm') it (Aux.det_raw_list l));
  Aux.mk_det_raw_cbor_inj_map l l';
  fold (cbor_det_array_iterator_match (pm +. pm') it l);
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t cbor_det_array_iterator_match
= (x: _) (#p: _) (#y: _)
{
  let lr = Ghost.hide (Aux.det_raw_list y);
  unfold (cbor_det_array_iterator_match p x y);
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Aux.det_raw_list y))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr));
  unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr));
  with l1 l2 . assert (
    I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.after l2);
  I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.before l1;
  I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.after l2;
  let len_before = I.base_mixed_list_length x.LowParse.PulseParse.Iterator.before;
  Aux.length_det_raw_list y;
  let res = (len_before = 0sz);
  fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr));
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Aux.det_raw_list y));
  fold (cbor_det_array_iterator_match p x y);
  res
}





(* ======== iterator_start ======== *)

#push-options "--z3rlimit 64"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_array_iterator_start (_: unit) : array_iterator_start_t cbor_det_match cbor_det_array_iterator_match
= (x: _) (#p: _) (#y: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  unfold (cbor_det_match p x y);
  let l_ghost : Ghost.erased (list Spec.cbor) = Spec.CArray?.v (Spec.unpack y);
  Aux.mk_det_raw_cbor_array_eq y (Ghost.reveal l_ghost);
  let ml = Access.cbor_raw_get_array p x ();
  with pm' lr . assert (
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml lr **
    Pulse.Lib.Trade.trade
      (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml lr)
      (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor y)));
  // lr == Array?.v (mk_det_raw_cbor y) == det_raw_list l_ghost
  rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml lr)
       as (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml (Aux.det_raw_list l_ghost));
  rewrite (Pulse.Lib.Trade.trade
      (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml lr)
      (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor y)))
       as (Pulse.Lib.Trade.trade
      (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml (Aux.det_raw_list l_ghost))
      (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor y)));
  let it = I.iterator_start
    RawMatch.cbor_raw_match
    SpecRawEverParse.parse_raw_data_item
    (Validate.jump_raw_data_item f64)
    pm'
    ml
    (Aux.det_raw_list l_ghost)
    cbor_raw_match_share_aux
    cbor_raw_match_gather_aux;
  with pm'' . assert (
    I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm'' it (Aux.det_raw_list l_ghost) **
    Pulse.Lib.Trade.trade
      (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm'' it (Aux.det_raw_list l_ghost))
      (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml (Aux.det_raw_list l_ghost)));
  Trade.trans _ _ (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor y));
  Trade.intro_trade
    (cbor_det_array_iterator_match pm'' it l_ghost)
    (cbor_det_match p x y)
    (Pulse.Lib.Trade.trade
      (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm'' it (Aux.det_raw_list l_ghost))
      (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor y)))
    fn _ {
      unfold (cbor_det_array_iterator_match pm'' it l_ghost);
      Trade.elim
        (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm'' it (Aux.det_raw_list l_ghost))
        (RawMatch.cbor_raw_match p x (SpecRaw.mk_det_raw_cbor y));
      fold (cbor_det_match p x y);
    };
  fold (cbor_det_array_iterator_match pm'' it l_ghost);
  it
}

#pop-options

(* ======== iterator_length, iterator_next (item 8 cont.) ======== *)

#push-options "--z3rlimit 64"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_array_iterator_length (_: unit) : array_iterator_length_t cbor_det_array_iterator_match
= (x: _) (#p: _) (#y: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let lr = Ghost.hide (Aux.det_raw_list y);
  unfold (cbor_det_array_iterator_match p x y);
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Aux.det_raw_list y))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr));
  unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr));
  with l1 l2 . assert (
    I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.after l2);
  I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.before l1;
  I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x.LowParse.PulseParse.Iterator.after l2;
  Aux.length_det_raw_list y;
  let len_before = I.base_mixed_list_length x.LowParse.PulseParse.Iterator.before;
  let len_after = I.mixed_list_length x.LowParse.PulseParse.Iterator.after;
  List.Tot.append_length l1 l2;
  SZ.fits_u64_implies_fits (SZ.v len_before + SZ.v len_after);
  let len_total = SZ.add len_before len_after;
  let res = SZ.sizet_to_uint64 len_total;
  fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr));
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Ghost.reveal lr))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p x (Aux.det_raw_list y));
  fold (cbor_det_array_iterator_match p x y);
  res
}

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_array_iterator_next (_: unit) : array_iterator_next_t cbor_det_match cbor_det_array_iterator_match
= (x: _) (#y: _) (#py: _) (#z: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let lr = Ghost.hide (Aux.det_raw_list z);
  unfold (cbor_det_array_iterator_match py y z);
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py y (Aux.det_raw_list z))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py y (Ghost.reveal lr));
  Aux.length_det_raw_list z;
  assert (pure (List.Tot.length (Ghost.reveal lr) == List.Tot.length z));
  assert (pure (Cons? (Ghost.reveal lr)));
  let zcp = LowParse.PulseParse.Base.zero_copy_parse_of_strong_prefix
    (CBOR.Pulse.Raw.EverParse.Read.cbor_raw_read 1.0R f64) ();
  let res = I.iterator_next
    RawMatch.cbor_raw_match
    SpecRawEverParse.parse_raw_data_item
    (Validate.jump_raw_data_item f64)
    py x y lr
    cbor_raw_match_share_aux
    cbor_raw_match_gather_aux
    zcp;
  unfold (I.iterator_next_post RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Ghost.reveal y) (Ghost.reveal lr) res);
  with pm_v hd_val tl_l it' pm' . assert (
    RawMatch.cbor_raw_match pm_v res hd_val **
    R.pts_to x it' **
    I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l **
    Trade.trade
      (RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
      (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (Ghost.reveal y) (Ghost.reveal lr))
  );
  Aux.list_map_mk_cbor_mk_det_raw_cbor z;
  Aux.list_map_mk_det_raw_cbor_correct z;
  // z == map mk_cbor lr; lr == hd_val :: tl_l
  // so z == mk_cbor hd_val :: map mk_cbor tl_l
  let v_hd : Ghost.erased Spec.cbor = Ghost.hide (SpecRaw.mk_cbor hd_val);
  let v_tl : Ghost.erased (list Spec.cbor) = Ghost.hide (List.Tot.map SpecRaw.mk_cbor tl_l);
  // hd_val and tl_l are in det_raw_list z, so each satisfies the optimal/sorted preds
  // (from list_map_mk_det_raw_cbor_correct on the for_all of cons).
  // hence mk_det_raw_cbor (mk_cbor hd_val) == hd_val.
  SpecRaw.mk_det_raw_cbor_mk_cbor hd_val;
  // For the tail: det_raw_list (map mk_cbor tl_l) == tl_l
  Aux.det_raw_list_inverse tl_l;
  // Show List.Tot.length tl_l < pow2 64 (since z < pow2 64 and tl_l shorter)
  Aux.length_det_raw_list v_tl;
  rewrite (RawMatch.cbor_raw_match pm_v res hd_val)
       as (cbor_det_match pm_v res v_hd);
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' (Aux.det_raw_list v_tl));
  fold (cbor_det_array_iterator_match pm' it' v_tl);
  // Build the final trade by manual intro_trade. The "extra" we carry is
  // the existing iterator_next trade.
  Trade.intro_trade
    (cbor_det_match pm_v res v_hd ** cbor_det_array_iterator_match pm' it' v_tl)
    (cbor_det_array_iterator_match py y z)
    (Trade.trade
      (RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
      (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (Ghost.reveal y) (Ghost.reveal lr)))
    fn _ {
      unfold (cbor_det_array_iterator_match pm' it' v_tl);
      rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' (Aux.det_raw_list v_tl))
           as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l);
      rewrite (cbor_det_match pm_v res v_hd)
           as (RawMatch.cbor_raw_match pm_v res hd_val);
      Trade.elim
        (RawMatch.cbor_raw_match pm_v res hd_val **
         I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
        (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (Ghost.reveal y) (Ghost.reveal lr));
      rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (Ghost.reveal y) (Ghost.reveal lr))
           as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py y (Aux.det_raw_list z));
      fold (cbor_det_array_iterator_match py y z);
    };
  res
}

#pop-options

(* ======== cbor_det_validate (item 1) — ports legacy validator ======== *)

module DetValidate = CBOR.Pulse.Raw.EverParse.Det.Validate

let cbor_det_validate_post_intro
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Lemma
  (requires (DetValidate.cbor_validate_det_post v res))
  (ensures (cbor_det_validate_post v res))
= Classical.forall_intro (Classical.move_requires SpecRaw.mk_det_raw_cbor_mk_cbor);
  assert (forall (v1: SpecRawBase.raw_data_item) . (CBOR.Spec.Raw.Optimal.raw_data_item_ints_optimal v1 /\ CBOR.Spec.Raw.Optimal.raw_data_item_sorted SpecF.deterministically_encoded_cbor_map_key_order v1) ==> SpecF.serialize_cbor v1 == Spec.cbor_det_serialize (SpecRaw.mk_cbor v1))

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_validate (_: unit) : cbor_det_validate_t
= (input: _)
  (#pm: _)
  (#v: _)
{
  let res = DetValidate.cbor_validate_det input;
  cbor_det_validate_post_intro v res;
  res
}

(* ======== cbor_det_parse_valid (item 2) ======== *)

let cbor_det_parse_aux_local
  (v: Seq.seq U8.t)
  (len: nat)
  (v1': SpecRawBase.raw_data_item {
    len <= Seq.length v /\
    Seq.slice v 0 len == SpecF.serialize_cbor v1'
  })
  (v1: Spec.cbor)
  (v2: Seq.seq U8.t)
: Lemma
  (v == Spec.cbor_det_serialize v1 `Seq.append` v2 ==> v1' == SpecRaw.mk_det_raw_cbor v1)
= Seq.lemma_split v len;
  Classical.move_requires (SpecF.serialize_cbor_inj (SpecRaw.mk_det_raw_cbor v1) v1' v2) (Seq.slice v len (Seq.length v))

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_parse_valid (_: unit) : cbor_det_parse_valid_t u#0 #_ cbor_det_match
= (input: _) (#pm: _) (#v: _)
{
  let len = Pulse.Lib.Slice.len input;
  Pulse.Lib.Slice.pts_to_len input;
  Classical.forall_intro cbor_det_parse_aux1;
  let res = DetValidate.cbor_parse_valid input;
  with v1' . assert (RawMatch.cbor_raw_match 1.0R res v1');
  Classical.forall_intro_2 (cbor_det_parse_aux_local v (SZ.v len) v1');
  rewrite each v1' as (SpecRaw.mk_det_raw_cbor (SpecRaw.mk_cbor v1'));
  fold (cbor_det_match 1.0R res (SpecRaw.mk_cbor v1'));
  res
}

(* ======== array_iterator_truncate (item 8 final) ======== *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --ext no:context_pruning"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_array_iterator_truncate (_: unit) : array_iterator_truncate_t cbor_det_array_iterator_match
= (x: _) (len: _) (#py: _) (#z: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let lr = Ghost.hide (Aux.det_raw_list z);
  let n = U64.v len;
  let len_sz = SZ.uint64_to_sizet len;
  unfold (cbor_det_array_iterator_match py x z);
  rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Aux.det_raw_list z))
       as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Ghost.reveal lr));
  unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Ghost.reveal lr));
  with l1 l2 . assert (
    I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.after l2);
  I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.before l1;
  I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.after l2;
  Aux.length_det_raw_list z;
  let cb_sz = I.base_mixed_list_length x.LowParse.PulseParse.Iterator.before;
  let len_before_sz = (if SZ.lte len_sz cb_sz then len_sz else cb_sz);
  let len_after_sz = (if SZ.lte len_sz cb_sz then 0sz else SZ.sub len_sz cb_sz);
  // Narrow before to first len_before_sz elements
  rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.before l1)
       as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py x.LowParse.PulseParse.Iterator.before l1);
  let bi' = I.base_mixed_list_narrow_n
    RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item
    (Validate.jump_raw_data_item f64) 0 (SZ.v cb_sz) py x.LowParse.PulseParse.Iterator.before l1
    0sz len_before_sz;
  // bi' : base_mixed_list cbor_raw with base_mixed_list_match bi' (list_narrow l1 0 (SZ.v len_before_sz)) at pm
  // plus trade (...) (base_mixed_list_match_n before)
  // Narrow after to first len_after_sz elements
  let ca_sz = I.mixed_list_length x.LowParse.PulseParse.Iterator.after;
  // Re-establish bounds: U64.v len <= List.Tot.length z = SZ.v cb_sz + SZ.v ca_sz
  List.Tot.append_length l1 l2;
  assert (pure (SZ.v len_after_sz <= SZ.v ca_sz));
  rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.after l2)
       as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py x.LowParse.PulseParse.Iterator.after l2);
  let after' = I.mixed_list_narrow_n
    RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item
    (Validate.jump_raw_data_item f64) 0 (SZ.v ca_sz) py x.LowParse.PulseParse.Iterator.after l2
    0sz len_after_sz
    cbor_raw_match_share_aux cbor_raw_match_gather_aux;
  // after' : mixed_list cbor_raw with mixed_list_match after' (list_narrow l2 0 (SZ.v len_after_sz)) at pm/2
  // Build new iterator at pm/2 (need to share before)
  // bi' is at full pm, but after' at pm/2. Share bi' to bring to pm/2.
  rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)))
       as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi' (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)));
  I.base_mixed_list_match_n_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi'
    (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)) cbor_raw_match_share_aux;
  // Now we have two copies of base_mixed_list_match_n (pm/2) bi' l1'.
  // Use one for the new iterator, gather the other back to satisfy the trade.
  // Actually: we need to give the trade a way to recover base_mixed_list_match before l1 at pm.
  // The trade for narrow: (base_mixed_list_match (pm) bi' l1') => (base_mixed_list_match_n 0 (SZ.v cb_sz) pm before l1).
  // We have two halves at pm/2. To use the trade we need to gather them first.
  // Actually let's keep it simple: the trade body can gather them inside.
  rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)))
       as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) bi' (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)));
  // Construct the truncated iterator
  let l1_narrow : Ghost.erased (list SpecRawBase.raw_data_item) = LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz);
  let l2_narrow : Ghost.erased (list SpecRawBase.raw_data_item) = LowParse.PulseParse.Iterator.list_narrow l2 0 (SZ.v len_after_sz);
  // Rewrite the second copy of base_mixed_list_match_n to use l1_narrow form
  rewrite each (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)) as (Ghost.reveal l1_narrow);
  rewrite each (LowParse.PulseParse.Iterator.list_narrow l2 0 (SZ.v len_after_sz)) as (Ghost.reveal l2_narrow);
  let it' : LowParse.PulseParse.Iterator.iterator RawType.cbor_raw = { before = bi'; after = after' };
  // Establish the truncated list relation
  // take n (l1 ++ l2) == l1_narrow ++ l2_narrow
  List.Tot.append_length l1 l2;
  // Use list_narrow_append: list_narrow (l1@l2) 0 n == list_narrow l1 0 (min n cb) @ list_narrow l2 0 (n - min n cb)
  LowParse.PulseParse.Iterator.list_narrow_append l1 l2 0 n;
  // Pure proof via splitAt-of-append properties
  assert (pure (
    LowParse.PulseParse.Iterator.list_narrow (Ghost.reveal lr) 0 n ==
    List.Tot.append (Ghost.reveal l1_narrow) (Ghost.reveal l2_narrow)));
  // Convert l_narrow into the spec form
  Aux.det_raw_list_take_eq z n;
  let z_take : Ghost.erased (list Spec.cbor) = Ghost.hide (fst (List.Tot.splitAt n z));
  // det_raw_list z_take == list_narrow lr 0 n
  assert (pure (Aux.det_raw_list z_take == LowParse.PulseParse.Iterator.list_narrow (Ghost.reveal lr) 0 n));
  // Rewrite the matches (l1_narrow ghost was already substituted by rewrite each above)
  rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) bi' (Ghost.reveal l1_narrow))
       as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.before (Ghost.reveal l1_narrow));
  rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) after' (Ghost.reveal l2_narrow))
       as (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.after (Ghost.reveal l2_narrow));
  fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it' (Aux.det_raw_list z_take));
  fold (cbor_det_array_iterator_match (py /. 2.0R) it' z_take);
  // Construct the trade back. The "extra" carries:
  //   - the second copy of base_mixed_list_match_n bi' at pm/2
  //   - the trade narrow_before (returns base_mixed_list_match_n before l1 at pm, given bi' at pm)
  //   - the trade narrow_after (returns mixed_list_match_n after l2 at pm, given after' at pm/2)
  Trade.intro_trade
    (cbor_det_array_iterator_match (py /. 2.0R) it' z_take)
    (cbor_det_array_iterator_match py x z)
    (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (Ghost.reveal l1_narrow) **
     Trade.trade
       (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow))
       (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py x.LowParse.PulseParse.Iterator.before l1) **
     Trade.trade
       (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) after' (Ghost.reveal l2_narrow))
       (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py x.LowParse.PulseParse.Iterator.after l2))
    fn _ {
      // Body: given cbor_det_array_iterator_match it' z_take, recover orig
      unfold (cbor_det_array_iterator_match (py /. 2.0R) it' z_take);
      rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it' (Aux.det_raw_list z_take))
           as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it' (List.Tot.append (Ghost.reveal l1_narrow) (Ghost.reveal l2_narrow)));
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it' (List.Tot.append (Ghost.reveal l1_narrow) (Ghost.reveal l2_narrow)));
      with xl1 xl2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.before xl1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.after xl2);
      // The split is uniquely determined: xl1 has length len_before_sz (from base_mixed_list_match_length on bi'), xl2 has length len_after_sz.
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.before xl1;
      I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.after xl2;
      // From xl1++xl2 == l1_narrow++l2_narrow with len(xl1)==len(l1_narrow), conclude xl1==l1_narrow and xl2==l2_narrow
      List.Tot.append_length (Ghost.reveal l1_narrow) (Ghost.reveal l2_narrow);
      List.Tot.append_length xl1 xl2;
      List.Tot.append_injective xl1 (Ghost.reveal l1_narrow) xl2 (Ghost.reveal l2_narrow);
      rewrite each xl1 as (Ghost.reveal l1_narrow);
      rewrite each xl2 as (Ghost.reveal l2_narrow);
      rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.before (Ghost.reveal l1_narrow))
           as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) bi' (Ghost.reveal l1_narrow));
      rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it'.LowParse.PulseParse.Iterator.after (Ghost.reveal l2_narrow))
           as (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) after' (Ghost.reveal l2_narrow));
      // Gather two pm/2 copies of bi' to pm
      rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) bi' (Ghost.reveal l1_narrow))
           as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (Ghost.reveal l1_narrow));
      I.base_mixed_list_match_n_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) (py /. 2.0R) bi' (Ghost.reveal l1_narrow) (Ghost.reveal l1_narrow) cbor_raw_match_gather_aux;
      drop_ (pure (Ghost.reveal l1_narrow == Ghost.reveal l1_narrow));
      rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R +. py /. 2.0R) bi' (Ghost.reveal l1_narrow))
           as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow));
      // Use trade narrow_before to recover the original before
      Trade.elim _ (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py x.LowParse.PulseParse.Iterator.before l1);
      // Use trade narrow_after on after'
      Trade.elim _ (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py x.LowParse.PulseParse.Iterator.after l2);
      // Fold back: original iterator_match
      rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py x.LowParse.PulseParse.Iterator.before l1)
           as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.before l1);
      rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py x.LowParse.PulseParse.Iterator.after l2)
           as (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x.LowParse.PulseParse.Iterator.after l2);
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Ghost.reveal lr));
      rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Ghost.reveal lr))
           as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x (Aux.det_raw_list z));
      fold (cbor_det_array_iterator_match py x z);
    };
  // Final shape: rewrite z_take to fst (splitAt (U64.v len) z) for the post
  rewrite each (Ghost.reveal z_take) as (fst (List.Tot.splitAt (U64.v len) z));
  it'
}

#pop-options

(* ======== API-level fragment-serializer wrappers (item 3 lift) ======== *)

module DetSer = CBOR.Pulse.Raw.EverParse.Det.Serialize
module RV = CBOR.Spec.Raw.Optimal

#push-options "--z3rlimit 32 --ext no:context_pruning"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_serialize_tag (_: unit) : cbor_det_serialize_tag_t
= (tag: U64.t) (output: _)
{
  let tag' = SpecRaw.mk_raw_uint64 tag;
  // Establish the equation Spec.cbor_det_serialize_tag tag == SpecF.serialize_cbor_tag tag'
  // (made visible by friend CBOR.Spec.API.Format).
  assert (pure (Spec.cbor_det_serialize_tag tag == SpecF.serialize_cbor_tag tag'));
  let res = DetSer.cbor_serialize_tag tag' output;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_serialize_string (_: unit) : cbor_det_serialize_string_t
= (ty: _) (off: U64.t) (out: _) (#v: _)
{
  let off' = SpecRaw.mk_raw_uint64 off;
  let l = Ghost.hide (Seq.slice v 0 (U64.v off));
  // The bridge: Spec.cbor_det_serialize (pack (CString ty l)) ==
  //             SpecF.serialize_cbor (String ty off' l)
  // Established by these spec lemmas below.
  Spec.cbor_det_serialize_string_length_gt ty (Ghost.reveal l);
  SpecRaw.mk_det_raw_cbor_mk_cbor (SpecRawBase.String ty off' (Ghost.reveal l));
  SpecRaw.mk_cbor_eq (SpecRawBase.String ty off' (Ghost.reveal l));
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRawBase.String ty off' (Ghost.reveal l));
  assert (pure (Spec.cbor_det_serialize (Spec.pack (Spec.CString ty (Ghost.reveal l)))
              == SpecF.serialize_cbor (SpecRawBase.String ty off' (Ghost.reveal l))));
  let res = DetSer.cbor_serialize_string () ty off' out;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_serialize_array (_: unit) : cbor_det_serialize_array_t
= (len: U64.t) (out: _) (l: _) (off: _)
{
  let len' = SpecRaw.mk_raw_uint64 len;
  let l' = Ghost.hide (Aux.det_raw_list l);
  // l' = List.Tot.map mk_det_raw_cbor l (via Aux.det_raw_list_eq SMTPat)
  // and cbor_det_serialize_list l = serialize_cbor_list (List.Tot.map mk_det_raw_cbor l)
  assert (pure (Spec.cbor_det_serialize_list l == SpecF.serialize_cbor_list (Ghost.reveal l')));
  // Bridge for the array's serialize equation
  Spec.cbor_det_serialize_array_length_gt_list l;
  Aux.list_map_mk_cbor_mk_det_raw_cbor l;
  Aux.list_map_mk_det_raw_cbor_correct l;
  let x : Ghost.erased SpecRawBase.raw_data_item = Ghost.hide (SpecRawBase.Array len' (Ghost.reveal l'));
  CBOR.Spec.Raw.Optimal.raw_data_item_sorted_optimal_valid SpecF.deterministically_encoded_cbor_map_key_order (Ghost.reveal x);
  SpecRaw.mk_cbor_eq (Ghost.reveal x);
  SpecRaw.mk_det_raw_cbor_mk_cbor (Ghost.reveal x);
  assert (pure (Spec.cbor_det_serialize (Spec.pack (Spec.CArray l))
              == SpecF.serialize_cbor (SpecRawBase.Array len' (Ghost.reveal l'))));
  let res = DetSer.cbor_serialize_array len' out l' off;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_serialize_map (_: unit) : cbor_det_serialize_map_t
= (len: U64.t) (out: _) (l: _) (off: _)
{
  let len' = SpecRaw.mk_raw_uint64 len;
  let l' = Ghost.hide (SpecRaw.mk_det_raw_cbor_map_raw l);
  // The precondition's length on l matches len'.value through cbor_map_length
  assert (pure (List.Tot.length (Ghost.reveal l') == U64.v len'.value));
  // Equation: cbor_det_serialize_map l == serialize_cbor_map l' (by friend)
  assert (pure (Spec.cbor_det_serialize_map l == SpecF.serialize_cbor_map (Ghost.reveal l')));
  Spec.cbor_det_serialize_map_length_gt_list l;
  // Bridge: mk_det_raw_cbor (pack (CMap l)) == Map len' l' via mk_cbor_eq_map
  let x : Ghost.erased Spec.cbor = Ghost.hide (Spec.pack (Spec.CMap l));
  SpecRaw.mk_cbor_eq_map (Ghost.reveal x);
  assert (pure (Spec.cbor_det_serialize (Spec.pack (Spec.CMap l))
              == SpecF.serialize_cbor (SpecRawBase.Map len' (Ghost.reveal l'))));
  let res = DetSer.cbor_serialize_map len' out l' off;
  res
}

#pop-options

(* ======== cbor_det_serialize_map_insert ======== *)

module Insert = CBOR.Pulse.Raw.EverParse.Insert

#push-options "--z3rlimit 64 --ext no:context_pruning"

let cbor_det_serialize_map_insert_pre_elim
  (m: Spec.cbor_map)
  (off2: SZ.t)
  (key: Spec.cbor)
  (off3: SZ.t)
  (value: Spec.cbor)
  (v: Seq.seq U8.t)
: Lemma
  (requires (cbor_det_serialize_map_insert_pre m off2 key off3 value v))
  (ensures (
    Insert.cbor_raw_map_insert_out_inv 0sz
      (SpecRaw.mk_det_raw_cbor_map_raw m) off2
      (SpecRaw.mk_det_raw_cbor key) off3
      (SpecRaw.mk_det_raw_cbor value) v
  ))
= Insert.cbor_raw_map_insert_out_inv_intro 0sz
    (SpecRaw.mk_det_raw_cbor_map_raw m) off2
    (SpecRaw.mk_det_raw_cbor key) off3
    (SpecRaw.mk_det_raw_cbor value) v

let cbor_det_serialize_map_insert_post_intro
  (m: Spec.cbor_map)
  (key: Spec.cbor)
  (value: Spec.cbor)
  (res: bool)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    Insert.cbor_raw_map_insert_post
      (SpecRaw.mk_det_raw_cbor_map_raw m)
      (SpecRaw.mk_det_raw_cbor key)
      (SpecRaw.mk_det_raw_cbor value) res v
  ))
  (ensures (cbor_det_serialize_map_insert_post m key value res v))
=
  Insert.cbor_raw_map_insert_post_elim
    (SpecRaw.mk_det_raw_cbor_map_raw m)
    (SpecRaw.mk_det_raw_cbor key)
    (SpecRaw.mk_det_raw_cbor value) res v;
  SpecRaw.mk_det_raw_cbor_map_raw_snoc m key value

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_serialize_map_insert (_: unit) : cbor_det_serialize_map_insert_t
= (out: _) (m: _) (off2: _) (key: _) (off3: _) (value: _)
{
  with v . assert (pts_to out v);
  let m' = Ghost.hide (SpecRaw.mk_det_raw_cbor_map_raw m);
  let key' = Ghost.hide (SpecRaw.mk_det_raw_cbor key);
  let value' = Ghost.hide (SpecRaw.mk_det_raw_cbor value);
  cbor_det_serialize_map_insert_pre_elim m off2 key off3 value v;
  let res = Insert.cbor_raw_map_insert out m' off2 key' off3 value';
  with v' . assert (pts_to out v');
  cbor_det_serialize_map_insert_post_intro m key value res v';
  res
}

#pop-options

(* ======== cbor_det_map_iterator_match ========

   Foundation for the map iterator family in Det.C.fst (currently
   admitted). The full set of operations (start, is_empty, next, share,
   gather, length) mirrors the array iterator (lines ~755–1052) but with
   the map-entry vmatch and the nondep_then(parse_raw_data_item, ...)
   parser. Implementing them is mechanical but bulky (~600 lines) and
   additionally requires a zero-copy parser for cbor_map_entry which has
   not yet been ported from the legacy CBOR.Pulse.Raw.Read.

   For now we just pin the type definition so future work can build
   on it without breaking call sites. *)

[@@pulse_unfold]
let cbor_det_map_iterator_match
  (pm: perm)
  (it: CBOR.Pulse.API.Det.Type.cbor_det_map_iterator_t)
  (l: list (Spec.cbor & Spec.cbor))
: Tot slprop
= I.iterator_match
    (fun (pm0: perm) (e: RawType.cbor_map_entry RawType.cbor_raw)
         (v: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
       RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    pm it
    (Aux.det_raw_map_entries l) **
  pure (FStar.UInt.fits (List.Tot.length l) U64.n)

(* Share/gather/is_empty/length helpers for the map entry vmatch *)

ghost
fn cbor_map_entry_match_share_aux
  (e: RawType.cbor_map_entry RawType.cbor_raw)
  (#pm0: perm)
  (#x2: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
  requires RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e x2
  ensures RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (pm0 /. 2.0R) e x2 **
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (pm0 /. 2.0R) e x2
{
  RawMatch.cbor_map_entry_match_share RawMatch.cbor_raw_match cbor_raw_match_share_aux e #pm0 #x2
}

ghost
fn cbor_map_entry_match_gather_aux
    (e: RawType.cbor_map_entry RawType.cbor_raw)
    (#pm0: perm)
    (#x2: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
    (#pm0': perm)
    (#x2': (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
  requires RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e x2 **
           RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0' e x2'
  ensures RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (pm0 +. pm0') e x2 **
          pure (x2 == x2')
{
  ghost fn cbor_raw_match_gather_explicit
      (x1: RawType.cbor_raw)
      (#pm00: perm)
      (#xa: SpecRawBase.raw_data_item)
      (#pm00': perm)
      (xb: SpecRawBase.raw_data_item { xb << x2' })
    requires RawMatch.cbor_raw_match pm00 x1 xa ** RawMatch.cbor_raw_match pm00' x1 xb
    ensures RawMatch.cbor_raw_match (pm00 +. pm00') x1 xa ** pure (xa == xb)
  {
    cbor_raw_match_gather_aux x1 #pm00 #xa #pm00' #xb
  };
  RawMatch.cbor_map_entry_match_gather RawMatch.cbor_raw_match e #pm0 #x2 #pm0' #x2'
    cbor_raw_match_gather_explicit
}

(* ---- map iterator share / gather ---- *)

ghost
fn cbor_det_map_iterator_share (_: unit) : share_t cbor_det_map_iterator_match
= (it: _) (#pm: _) (#l: _)
{
  let lr = Ghost.hide (Aux.det_raw_map_entries l);
  unfold (cbor_det_map_iterator_match pm it l);
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it (Aux.det_raw_map_entries l))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it (Ghost.reveal lr));
  unfold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it (Ghost.reveal lr));
  with l1 l2 . assert (
    I.base_mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it.LowParse.PulseParse.Iterator.after l2);
  I.base_mixed_list_match_share
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    pm it.LowParse.PulseParse.Iterator.before l1 cbor_map_entry_match_share_aux;
  I.mixed_list_match_share
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    pm it.LowParse.PulseParse.Iterator.after l2 cbor_map_entry_match_share_aux;
  fold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm /. 2.0R) it (Ghost.reveal lr));
  fold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm /. 2.0R) it (Ghost.reveal lr));
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm /. 2.0R) it (Ghost.reveal lr))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm /. 2.0R) it (Aux.det_raw_map_entries l));
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm /. 2.0R) it (Ghost.reveal lr))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm /. 2.0R) it (Aux.det_raw_map_entries l));
  fold (cbor_det_map_iterator_match (pm /. 2.0R) it l);
  fold (cbor_det_map_iterator_match (pm /. 2.0R) it l);
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t cbor_det_map_iterator_match
= (x: _) (#p: _) (#y: _)
{
  let lr = Ghost.hide (Aux.det_raw_map_entries y);
  unfold (cbor_det_map_iterator_match p x y);
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x (Aux.det_raw_map_entries y))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x (Ghost.reveal lr));
  unfold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x (Ghost.reveal lr));
  with l1 l2 . assert (
    I.base_mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x.LowParse.PulseParse.Iterator.after l2);
  I.base_mixed_list_match_length
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    p x.LowParse.PulseParse.Iterator.before l1;
  I.mixed_list_match_length
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    p x.LowParse.PulseParse.Iterator.after l2;
  let len_before = I.base_mixed_list_length x.LowParse.PulseParse.Iterator.before;
  Aux.length_det_raw_map_entries y;
  let res = (len_before = 0sz);
  fold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x (Ghost.reveal lr));
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x (Ghost.reveal lr))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p x (Aux.det_raw_map_entries y));
  fold (cbor_det_map_iterator_match p x y);
  res
}

ghost
fn cbor_det_map_iterator_gather (_: unit) : gather_t cbor_det_map_iterator_match
= (it: _) (#pm: _) (#l: _) (#pm': _) (#l': _)
{
  let lr  = Ghost.hide (Aux.det_raw_map_entries l);
  let lr' = Ghost.hide (Aux.det_raw_map_entries l');
  unfold (cbor_det_map_iterator_match pm it l);
  unfold (cbor_det_map_iterator_match pm' it l');
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it (Aux.det_raw_map_entries l))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it (Ghost.reveal lr));
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it (Aux.det_raw_map_entries l'))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it (Ghost.reveal lr'));
  unfold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it (Ghost.reveal lr));
  unfold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it (Ghost.reveal lr'));
  with l1 l2 . assert (
    I.base_mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it.LowParse.PulseParse.Iterator.before l1 **
    I.mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it.LowParse.PulseParse.Iterator.after l2);
  with l1' l2' . assert (
    I.base_mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it.LowParse.PulseParse.Iterator.before l1' **
    I.mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it.LowParse.PulseParse.Iterator.after l2');
  I.base_mixed_list_match_gather
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    pm pm' it.LowParse.PulseParse.Iterator.before l1 l1' cbor_map_entry_match_gather_aux;
  I.mixed_list_match_gather
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    pm pm' it.LowParse.PulseParse.Iterator.after l2 l2' cbor_map_entry_match_gather_aux;
  List.Tot.append_injective l1 l1' l2 l2';
  fold (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm +. pm') it (Ghost.reveal lr));
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm +. pm') it (Ghost.reveal lr))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      (pm +. pm') it (Aux.det_raw_map_entries l));
  // l == l' from injectivity of det_raw_map_entries
  Aux.mk_det_raw_cbor_inj_map_entries l l';
  fold (cbor_det_map_iterator_match (pm +. pm') it l);
}

(* ---- map iterator next ---- *)

module ReadMapEntry = CBOR.Pulse.Raw.EverParse.ReadMapEntry

#push-options "--z3rlimit 256 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_map_iterator_next (_: unit) : map_iterator_next_t cbor_det_map_entry_match cbor_det_map_iterator_match
= (x: _) (#y: _) (#py: _) (#z: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let lr = Ghost.hide (Aux.det_raw_map_entries z);
  unfold (cbor_det_map_iterator_match py y z);
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      py y (Aux.det_raw_map_entries z))
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      py y (Ghost.reveal lr));
  Aux.length_det_raw_map_entries z;
  assert (pure (Cons? (Ghost.reveal lr)));
  let zcp = LowParse.PulseParse.Base.zero_copy_parse_of_strong_prefix
    (ReadMapEntry.cbor_raw_read_map_entry 1.0R f64) ();
  let res = I.iterator_next
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    (LowParse.Pulse.Combinators.jump_nondep_then (Validate.jump_raw_data_item f64) (Validate.jump_raw_data_item f64))
    py x y lr
    cbor_map_entry_match_share_aux
    cbor_map_entry_match_gather_aux
    zcp;
  unfold (I.iterator_next_post
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    py x (Ghost.reveal y) (Ghost.reveal lr) res);
  with pm_v hd_val tl_l it' pm' . assert (
    RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
    R.pts_to x it' **
    I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it' tl_l **
    Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match
         (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         pm' it' tl_l)
      (I.iterator_match
         (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         py (Ghost.reveal y) (Ghost.reveal lr))
  );
  Aux.list_map_mk_cbor_mk_det_raw_cbor_map_entry z;
  Aux.list_map_mk_det_raw_cbor_correct_map_entries z;
  // z == map mk_cbor_map_entry lr; lr == hd_val :: tl_l
  // so z == mk_cbor_map_entry hd_val :: map mk_cbor_map_entry tl_l
  let v_hd : Ghost.erased (Spec.cbor & Spec.cbor) = Ghost.hide (SpecRaw.mk_cbor_map_entry hd_val);
  let v_tl : Ghost.erased (list (Spec.cbor & Spec.cbor)) = Ghost.hide (List.Tot.map SpecRaw.mk_cbor_map_entry tl_l);
  // hd_val and tl_l are in det_raw_map_entries z, so each satisfies the optimal/sorted preds
  Aux.mk_det_raw_cbor_map_entry_mk_cbor_map_entry hd_val;
  // For the tail: det_raw_map_entries (map mk_cbor_map_entry tl_l) == tl_l
  Aux.det_raw_map_entries_inverse tl_l;
  // Show List.Tot.length tl_l < pow2 64
  Aux.length_det_raw_map_entries v_tl;
  rewrite (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val)
       as (cbor_det_map_entry_match pm_v res v_hd);
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it' tl_l)
       as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it' (Aux.det_raw_map_entries v_tl));
  fold (cbor_det_map_iterator_match pm' it' v_tl);
  // Build the final trade
  Trade.intro_trade
    (cbor_det_map_entry_match pm_v res v_hd ** cbor_det_map_iterator_match pm' it' v_tl)
    (cbor_det_map_iterator_match py y z)
    (Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match
         (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         pm' it' tl_l)
      (I.iterator_match
         (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         py (Ghost.reveal y) (Ghost.reveal lr)))
    fn _ {
      unfold (cbor_det_map_iterator_match pm' it' v_tl);
      rewrite (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          pm' it' (Aux.det_raw_map_entries v_tl))
           as (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          pm' it' tl_l);
      rewrite (cbor_det_map_entry_match pm_v res v_hd)
           as (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val);
      Trade.elim
        (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
         I.iterator_match
           (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
           (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
           pm' it' tl_l)
        (I.iterator_match
           (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
           (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
           py (Ghost.reveal y) (Ghost.reveal lr));
      rewrite (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py (Ghost.reveal y) (Ghost.reveal lr))
           as (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py y (Aux.det_raw_map_entries z));
      fold (cbor_det_map_iterator_match py y z);
    };
  res
}

#pop-options


