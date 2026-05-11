module CBOR.Pulse.Raw.EverParse.Make
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open CBOR.Spec.Raw.Optimal

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator

(* ================================================================ *)
(* Helper: fold cbor_raw_match from cbor_raw_match_content           *)
(* ================================================================ *)

(* Given cbor_raw_match_content for the "other" case (simple/int), fold to cbor_raw_match.
   For simple/int, the content is unit and the slprop is emp. *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn cbor_raw_match_fold_from_content_emp
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
  (sq: squash (
    cbor_raw_get_header xl == Some (dfst (synth_raw_data_item_recip xh)) /\
    (let (| b, _ |) = dfst (synth_raw_data_item_recip xh) in
     b.major_type <> cbor_major_type_byte_string /\
     b.major_type <> cbor_major_type_text_string /\
     b.major_type <> cbor_major_type_array /\
     b.major_type <> cbor_major_type_map /\
     b.major_type <> cbor_major_type_tagged)
  ))
requires emp
ensures cbor_raw_match pm xl xh
{
  rewrite emp
    as (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
         (dfst (synth_raw_data_item_recip xh)) xl (dsnd (synth_raw_data_item_recip xh)));
  fold (cbor_raw_match_header (cbor_raw_id_proj.pair_proj_get xl) (dfst (synth_raw_data_item_recip xh)));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip xh));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl xh);
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  cbor_raw_match_fold_aux xl;
}

#pop-options

(* ================================================================ *)
(* mk_simple_value                                                   *)
(* ================================================================ *)

fn cbor_mk_simple_value
  (v: simple_value)
requires emp
returns res: cbor_raw
ensures cbor_raw_match 1.0R res (Simple v)
{
  let res = CBOR_Case_Simple v;
  cbor_raw_match_fold_from_content_emp 1.0R res (Simple v) ();
  res
}

(* ================================================================ *)
(* mk_int64                                                          *)
(* ================================================================ *)

fn cbor_mk_int64
  (ty: major_type_uint64_or_neg_int64)
  (v: U64.t)
requires emp
returns res: cbor_raw
ensures cbor_raw_match 1.0R res (Int64 ty (mk_raw_uint64 v))
{
  let i = { cbor_int_type = ty;
            cbor_int_size = (mk_raw_uint64 v).size;
            cbor_int_value = v };
  let res = CBOR_Case_Int i;
  cbor_raw_match_fold_from_content_emp 1.0R res (Int64 ty (mk_raw_uint64 v)) ();
  res
}

(* ================================================================ *)
(* mk_string                                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn cbor_raw_match_fold_from_content_string
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
  (sq: squash (
    cbor_raw_get_header xl == Some (dfst (synth_raw_data_item_recip xh)) /\
    (let (| b, _ |) = dfst (synth_raw_data_item_recip xh) in
     b.major_type = cbor_major_type_byte_string \/ b.major_type = cbor_major_type_text_string)
  ))
requires cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
    (dfst (synth_raw_data_item_recip xh)) xl (dsnd (synth_raw_data_item_recip xh))
ensures cbor_raw_match pm xl xh
{
  fold (cbor_raw_match_header (cbor_raw_id_proj.pair_proj_get xl) (dfst (synth_raw_data_item_recip xh)));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip xh));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl xh);
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  cbor_raw_match_fold_aux xl;
}

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

fn cbor_mk_string
  (f64: squash SZ.fits_u64)
  (ty: major_type_byte_string_or_text_string)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires S.pts_to s #p v ** pure (
    FStar.UInt.fits (Seq.length v) 64 /\
    (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
  )
returns res: cbor_raw
ensures exists* xh .
  cbor_raw_match 1.0R res xh **
  Trade.trade
    (cbor_raw_match 1.0R res xh)
    (S.pts_to s #p v)
{
  S.pts_to_len s;
  let the_prop =
    FStar.UInt.fits (Seq.length v) 64 /\
    (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v);
  let sq = elim_pure_explicit the_prop;
  let len64 = SZ.sizet_to_uint64 (S.len s);
  let ru = mk_raw_uint64 len64;
  // Share the pts_to into two halves
  S.share s;
  let str : cbor_string = {
    cbor_string_type = ty;
    cbor_string_size = ru.size;
    cbor_string_ptr = s;
    cbor_string_perm = p /. 2.0R;
  };
  let res = CBOR_Case_String str;
  let xh : Ghost.erased raw_data_item = String ty ru v;
  cbor_raw_match_content_eq_string cbor_raw_match parse_raw_data_item 1.0R
    (dfst (dfst (synth_raw_data_item_recip xh)))
    (dsnd (dfst (synth_raw_data_item_recip xh)))
    str
    (dsnd (synth_raw_data_item_recip xh));
  rewrite (S.pts_to s #(p /. 2.0R) v)
    as (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
         (dfst (synth_raw_data_item_recip xh)) res (dsnd (synth_raw_data_item_recip xh)));
  cbor_raw_match_fold_from_content_string 1.0R res xh ();
  // Create the trade with the other half as extra
  Trade.intro_trade
    (cbor_raw_match 1.0R res xh)
    (S.pts_to s #p v)
    (S.pts_to s #(p /. 2.0R) v)
    fn _ {
      rewrite (cbor_raw_match 1.0R res (Ghost.reveal xh))
        as (cbor_raw_match 1.0R (CBOR_Case_String str) (Ghost.reveal xh));
      cbor_raw_match_string_unfold_no_trade str;
      with v' . assert (S.pts_to str.cbor_string_ptr #(1.0R *. str.cbor_string_perm) v');
      rewrite (S.pts_to str.cbor_string_ptr #(1.0R *. str.cbor_string_perm) v')
        as (S.pts_to s #(p /. 2.0R) v');
      S.gather s;
      // gather gives: S.pts_to s #(p /. 2.0R +. p /. 2.0R) v ** pure (v == v')
      with _perm _val . assert (S.pts_to s #_perm _val);
      rewrite (S.pts_to s #_perm _val)
        as (S.pts_to s #p v);
    };
  res
}

#pop-options

(* ================================================================ *)
(* mk_tagged                                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

ghost
fn cbor_raw_match_fold_from_content_tagged
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
  (sq: squash (
    cbor_raw_get_header xl == Some (dfst (synth_raw_data_item_recip xh)) /\
    (let (| b, _ |) = dfst (synth_raw_data_item_recip xh) in
     b.major_type = cbor_major_type_tagged)
  ))
requires cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
    (dfst (synth_raw_data_item_recip xh)) xl (dsnd (synth_raw_data_item_recip xh))
ensures cbor_raw_match pm xl xh
{
  fold (cbor_raw_match_header (cbor_raw_id_proj.pair_proj_get xl) (dfst (synth_raw_data_item_recip xh)));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip xh));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl xh);
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  cbor_raw_match_fold_aux xl;
}

#pop-options

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

fn cbor_mk_tagged
  (tag: U64.t)
  (r: R.ref cbor_raw)
  (#pr: perm)
  (#child: Ghost.erased cbor_raw)
  (#pv: perm)
  (#child_xh: Ghost.erased raw_data_item)
requires R.pts_to r #pr child ** cbor_raw_match pv child child_xh
returns res: cbor_raw
ensures
  cbor_raw_match 1.0R res (Tagged (mk_raw_uint64 tag) child_xh) **
  Trade.trade
    (cbor_raw_match 1.0R res (Tagged (mk_raw_uint64 tag) child_xh))
    (R.pts_to r #pr child ** cbor_raw_match pv child child_xh)
{
  let ru = mk_raw_uint64 tag;
  // Share both resources to keep half as extra for the trade
  R.share r;
  cbor_raw_match_share child;
  let tv : cbor_tagged cbor_raw = {
    cbor_tagged_tag = ru;
    cbor_tagged_ptr = r;
    cbor_tagged_ref_perm = pr /. 2.0R;
    cbor_tagged_payload_perm = pv /. 2.0R;
  };
  let res = CBOR_Case_Tagged tv;
  let xh : Ghost.erased raw_data_item = Tagged ru child_xh;
  // Rewrite to use tv field projections so the fold can match
  rewrite (R.pts_to r #(pr /. 2.0R) child)
    as (R.pts_to tv.cbor_tagged_ptr #(1.0R *. tv.cbor_tagged_ref_perm) child);
  rewrite (cbor_raw_match (pv /. 2.0R) child child_xh)
    as (cbor_raw_match (1.0R *. tv.cbor_tagged_payload_perm) child child_xh);
  fold (vmatch_ref
    (fun (vl: cbor_raw) (vh: raw_data_item) ->
      cbor_raw_match (1.0R *. tv.cbor_tagged_payload_perm) vl vh)
    ({ v = tv.cbor_tagged_ptr; p = 1.0R *. tv.cbor_tagged_ref_perm })
    (Ghost.reveal child_xh));
  fold (cbor_tagged_content_slprop cbor_raw_match 1.0R tv (Ghost.reveal child_xh));
  rewrite (cbor_tagged_content_slprop cbor_raw_match 1.0R tv (Ghost.reveal child_xh))
    as (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
         (dfst (synth_raw_data_item_recip xh)) res (dsnd (synth_raw_data_item_recip xh)));
  cbor_raw_match_fold_from_content_tagged 1.0R res xh ();
  // Build the trade: extra = halved R.pts_to and cbor_raw_match
  Trade.intro_trade
    (cbor_raw_match 1.0R res (Ghost.reveal xh))
    (R.pts_to r #pr child ** cbor_raw_match pv child child_xh)
    (R.pts_to r #(pr /. 2.0R) child ** cbor_raw_match (pv /. 2.0R) child child_xh)
    fn _ {
      cbor_raw_match_unfold_aux res;
      unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match 1.0R res (Ghost.reveal xh));
      unfold (vmatch_synth
        (vmatch_dep_pair_with_proj
           cbor_raw_match_header
           cbor_raw_id_proj
           (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R))
        synth_raw_data_item_recip
        res (Ghost.reveal xh));
      unfold (vmatch_dep_pair_with_proj
        cbor_raw_match_header
        cbor_raw_id_proj
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R)
        res
        (synth_raw_data_item_recip (Ghost.reveal xh)));
      unfold (cbor_raw_match_header
        (cbor_raw_id_proj.pair_proj_get res)
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
      let the_header_prop = cbor_raw_get_header res == Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)));
      let _sq = elim_pure_explicit the_header_prop;
      rewrite (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
                 (dfst (synth_raw_data_item_recip (Ghost.reveal xh))) res
                 (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
        as (cbor_tagged_content_slprop cbor_raw_match 1.0R tv (Ghost.reveal child_xh));
      unfold (cbor_tagged_content_slprop cbor_raw_match 1.0R tv (Ghost.reveal child_xh));
      unfold (vmatch_ref
        (fun (vl: cbor_raw) (vh: raw_data_item) ->
          cbor_raw_match (1.0R *. tv.cbor_tagged_payload_perm) vl vh)
        ({ v = tv.cbor_tagged_ptr; p = 1.0R *. tv.cbor_tagged_ref_perm })
        (Ghost.reveal child_xh));
      with xl0 . assert (R.pts_to tv.cbor_tagged_ptr #(1.0R *. tv.cbor_tagged_ref_perm) xl0);
      rewrite (R.pts_to tv.cbor_tagged_ptr #(1.0R *. tv.cbor_tagged_ref_perm) xl0)
        as (R.pts_to r #(pr /. 2.0R) xl0);
      rewrite (cbor_raw_match (1.0R *. tv.cbor_tagged_payload_perm) xl0 child_xh)
        as (cbor_raw_match (pv /. 2.0R) xl0 child_xh);
      // Gather R.pts_to halves to prove xl0 == child
      R.gather r;
      rewrite (R.pts_to r #(pr /. 2.0R +. pr /. 2.0R) xl0) as (R.pts_to r #pr xl0);
      let sq = elim_pure_explicit (Ghost.reveal xl0 == Ghost.reveal child);
      rewrite (R.pts_to r #pr xl0) as (R.pts_to r #pr child);
      rewrite (cbor_raw_match (pv /. 2.0R) xl0 child_xh)
        as (cbor_raw_match (pv /. 2.0R) child child_xh);
      // Gather cbor_raw_match halves
      cbor_raw_match_gather child;
      rewrite (cbor_raw_match (pv /. 2.0R +. pv /. 2.0R) child child_xh)
        as (cbor_raw_match pv child child_xh);
      drop_ (pure (child_xh == child_xh));
    };
  rewrite (cbor_raw_match 1.0R res (Ghost.reveal xh))
    as (cbor_raw_match 1.0R res (Tagged (mk_raw_uint64 tag) child_xh));
  rewrite (Trade.trade
      (cbor_raw_match 1.0R res (Ghost.reveal xh))
      (R.pts_to r #pr child ** cbor_raw_match pv child child_xh))
    as (Trade.trade
      (cbor_raw_match 1.0R res (Tagged (mk_raw_uint64 tag) child_xh))
      (R.pts_to r #pr child ** cbor_raw_match pv child child_xh));
  res
}

#pop-options

(* ================================================================ *)
(* mk_map_entry                                                      *)
(* ================================================================ *)

(* Map entry constructor: given key and value with SAME permission pm,
   creates a map entry matched at permission pm. The trade returns
   cbor_raw_match pm for both key and value.
   
   For the full API (mk_map_entry_t with arbitrary pk, pv and result at 1.0R),
   a perm-reset mechanism is needed, which is implemented at the API layer. *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

fn cbor_mk_map_entry
  (xk: cbor_raw)
  (xv: cbor_raw)
  (#pm: perm)
  (#vk: Ghost.erased raw_data_item)
  (#vv: Ghost.erased raw_data_item)
requires cbor_raw_match pm xk vk ** cbor_raw_match pm xv vv
returns res: cbor_map_entry cbor_raw
ensures
  cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal vk, Ghost.reveal vv) **
  Trade.trade
    (cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal vk, Ghost.reveal vv))
    (cbor_raw_match pm xk vk ** cbor_raw_match pm xv vv)
{
  let res : cbor_map_entry cbor_raw = {
    cbor_map_entry_key = xk;
    cbor_map_entry_value = xv;
  };
  // Rewrite to projector forms for fold
  rewrite (cbor_raw_match pm xv vv)
    as (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get res) (snd (Ghost.reveal vk, Ghost.reveal vv)));
  fold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj res (snd (Ghost.reveal vk, Ghost.reveal vv)));
  rewrite (cbor_raw_match pm xk vk)
    as (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get res) (fst (Ghost.reveal vk, Ghost.reveal vv)));
  fold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) res (Ghost.reveal vk, Ghost.reveal vv));
  fold (cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal vk, Ghost.reveal vv));
  Trade.intro_trade
    (cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal vk, Ghost.reveal vv))
    (cbor_raw_match pm xk vk ** cbor_raw_match pm xv vv)
    emp
    fn _ {
      unfold (cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal vk, Ghost.reveal vv));
      unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
        (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) res (Ghost.reveal vk, Ghost.reveal vv));
      unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj res (snd (Ghost.reveal vk, Ghost.reveal vv)));
      rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get res) (fst (Ghost.reveal vk, Ghost.reveal vv)))
        as (cbor_raw_match pm xk vk);
      rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get res) (snd (Ghost.reveal vk, Ghost.reveal vv)))
        as (cbor_raw_match pm xv vv);
    };
  res
}

#pop-options

(* ================================================================ *)
(* mk_array                                                          *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

ghost
fn cbor_raw_match_fold_from_content_array
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
  (sq: squash (
    cbor_raw_get_header xl == Some (dfst (synth_raw_data_item_recip xh)) /\
    (let (| b, _ |) = dfst (synth_raw_data_item_recip xh) in
     b.major_type = cbor_major_type_array)
  ))
requires cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
    (dfst (synth_raw_data_item_recip xh)) xl (dsnd (synth_raw_data_item_recip xh))
ensures cbor_raw_match pm xl xh
{
  fold (cbor_raw_match_header (cbor_raw_id_proj.pair_proj_get xl) (dfst (synth_raw_data_item_recip xh)));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip xh));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl xh);
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  cbor_raw_match_fold_aux xl;
}

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

fn cbor_mk_array
  (f64: squash SZ.fits_u64)
  (len_size: integer_size)
  (ml: I.mixed_list cbor_raw)
  (#pm: perm)
  (#l: Ghost.erased (list raw_data_item))
requires
  I.mixed_list_match cbor_raw_match parse_raw_data_item pm ml l **
  pure (
    let len = SZ.v (I.mixed_list_length ml) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop len_size (U64.uint_to_t len) /\
    List.Tot.length l == len
  )
returns res: cbor_raw
ensures exists* xh .
  cbor_raw_match 1.0R res xh **
  Trade.trade
    (cbor_raw_match 1.0R res xh)
    (I.mixed_list_match cbor_raw_match parse_raw_data_item pm ml l)
{
  let the_prop =
    (let len = SZ.v (I.mixed_list_length ml) in
     FStar.UInt.fits len 64 /\
     raw_uint64_size_prop len_size (U64.uint_to_t len) /\
     List.Tot.length l == len);
  let sq = elim_pure_explicit the_prop;
  let len_sz = I.mixed_list_length ml;
  let len64 = SZ.sizet_to_uint64 len_sz;
  let ru : raw_uint64 = { size = len_size; value = len64 };
  let v : cbor_array cbor_raw = {
    cbor_array_length_size = len_size;
    cbor_array_ptr = ml;
    cbor_array_slice_perm = pm;
  };
  let res = CBOR_Case_Array v;
  let xh : Ghost.erased raw_data_item = Array ru l;
  cbor_raw_match_content_eq_array cbor_raw_match parse_raw_data_item 1.0R
    (dfst (dfst (synth_raw_data_item_recip xh)))
    (dsnd (dfst (synth_raw_data_item_recip xh)))
    v
    (dsnd (synth_raw_data_item_recip xh));
  rewrite
    (I.mixed_list_match cbor_raw_match parse_raw_data_item pm ml l)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
       (dfst (synth_raw_data_item_recip xh)) res (dsnd (synth_raw_data_item_recip xh)));
  cbor_raw_match_fold_from_content_array 1.0R res xh ();
  // Trade: unfold cbor_raw_match back to mixed_list_match
  Trade.intro_trade
    (cbor_raw_match 1.0R res xh)
    (I.mixed_list_match cbor_raw_match parse_raw_data_item pm ml l)
    emp
    fn _ {
      rewrite (cbor_raw_match 1.0R res (Ghost.reveal xh))
        as (cbor_raw_match 1.0R (CBOR_Case_Array v) (Ghost.reveal xh));
      let x : cbor_raw = CBOR_Case_Array v;
      rewrite (cbor_raw_match 1.0R (CBOR_Case_Array v) (Ghost.reveal xh))
        as (cbor_raw_match 1.0R x (Ghost.reveal xh));
      cbor_raw_match_unfold_aux x;
      unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match 1.0R x (Ghost.reveal xh));
      unfold (vmatch_synth
        (vmatch_dep_pair_with_proj
           cbor_raw_match_header
           cbor_raw_id_proj
           (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R))
        synth_raw_data_item_recip
        x (Ghost.reveal xh));
      unfold (vmatch_dep_pair_with_proj
        cbor_raw_match_header
        cbor_raw_id_proj
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R)
        x
        (synth_raw_data_item_recip (Ghost.reveal xh)));
      unfold (cbor_raw_match_header
        (cbor_raw_id_proj.pair_proj_get x)
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
      drop_ (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
             Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
      cbor_raw_match_content_eq_array cbor_raw_match parse_raw_data_item 1.0R
        (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
        (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)));
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
          (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
          x
          (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
        as
        (I.mixed_list_match cbor_raw_match parse_raw_data_item pm ml l);
    };
  res
}

#pop-options

(* ================================================================ *)
(* mk_map                                                            *)
(* ================================================================ *)


#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

ghost
fn cbor_raw_match_fold_from_content_map
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
  (sq: squash (
    cbor_raw_get_header xl == Some (dfst (synth_raw_data_item_recip xh)) /\
    (let (| b, _ |) = dfst (synth_raw_data_item_recip xh) in
     b.major_type = cbor_major_type_map)
  ))
requires cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
    (dfst (synth_raw_data_item_recip xh)) xl (dsnd (synth_raw_data_item_recip xh))
ensures cbor_raw_match pm xl xh
{
  fold (cbor_raw_match_header (cbor_raw_id_proj.pair_proj_get xl) (dfst (synth_raw_data_item_recip xh)));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip xh));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl xh);
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  cbor_raw_match_fold_aux xl;
}

fn cbor_mk_map
  (f64: squash SZ.fits_u64)
  (len_size: integer_size)
  (ml: I.mixed_list (cbor_map_entry cbor_raw))
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.mixed_list_match
    (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
      cbor_map_entry_match cbor_raw_match pm' elem x)
    (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  pure (
    let len = SZ.v (I.mixed_list_length ml) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop len_size (U64.uint_to_t len) /\
    List.Tot.length l == len
  )
returns res: cbor_raw
ensures exists* xh .
  cbor_raw_match 1.0R res xh **
  Trade.trade
    (cbor_raw_match 1.0R res xh)
    (I.mixed_list_match
      (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm' elem x)
      (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
{
  let the_prop =
    (let len = SZ.v (I.mixed_list_length ml) in
     FStar.UInt.fits len 64 /\
     raw_uint64_size_prop len_size (U64.uint_to_t len) /\
     List.Tot.length l == len);
  let sq = elim_pure_explicit the_prop;
  let len_sz = I.mixed_list_length ml;
  let len64 = SZ.sizet_to_uint64 len_sz;
  let ru : raw_uint64 = { size = len_size; value = len64 };
  let v : cbor_map cbor_raw = {
    cbor_map_length_size = len_size;
    cbor_map_ptr = ml;
    cbor_map_slice_perm = pm;
  };
  let res = CBOR_Case_Map v;
  let xh : Ghost.erased raw_data_item = Map ru l;
  cbor_raw_match_content_eq_map cbor_raw_match parse_raw_data_item 1.0R
    (dfst (dfst (synth_raw_data_item_recip xh)))
    (dsnd (dfst (synth_raw_data_item_recip xh)))
    v
    (dsnd (synth_raw_data_item_recip xh));
  rewrite
    (I.mixed_list_match
      (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm' elem x)
      (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
       (dfst (synth_raw_data_item_recip xh)) res (dsnd (synth_raw_data_item_recip xh)));
  cbor_raw_match_fold_from_content_map 1.0R res xh ();
  // Trade: unfold cbor_raw_match back to mixed_list_match
  Trade.intro_trade
    (cbor_raw_match 1.0R res xh)
    (I.mixed_list_match
      (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm' elem x)
      (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    emp
    fn _ {
      rewrite (cbor_raw_match 1.0R res (Ghost.reveal xh))
        as (cbor_raw_match 1.0R (CBOR_Case_Map v) (Ghost.reveal xh));
      let x : cbor_raw = CBOR_Case_Map v;
      rewrite (cbor_raw_match 1.0R (CBOR_Case_Map v) (Ghost.reveal xh))
        as (cbor_raw_match 1.0R x (Ghost.reveal xh));
      cbor_raw_match_unfold_aux x;
      unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match 1.0R x (Ghost.reveal xh));
      unfold (vmatch_synth
        (vmatch_dep_pair_with_proj
           cbor_raw_match_header
           cbor_raw_id_proj
           (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R))
        synth_raw_data_item_recip
        x (Ghost.reveal xh));
      unfold (vmatch_dep_pair_with_proj
        cbor_raw_match_header
        cbor_raw_id_proj
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R)
        x
        (synth_raw_data_item_recip (Ghost.reveal xh)));
      unfold (cbor_raw_match_header
        (cbor_raw_id_proj.pair_proj_get x)
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
      drop_ (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
             Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
      cbor_raw_match_content_eq_map cbor_raw_match parse_raw_data_item 1.0R
        (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
        (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)));
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
          (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
          x
          (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
        as
        (I.mixed_list_match
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm' elem x)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
    };
  res
}

#pop-options
