module CBOR.Pulse.Raw.EverParse.ArrayBuilder
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
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module Access = CBOR.Pulse.Raw.EverParse.Access
module Make = CBOR.Pulse.Raw.EverParse.Make
module Append = LowParse.PulseParse.Iterator.Append

(* ================================================================ *)
(* Minimal integer_size for a given length                          *)
(* ================================================================ *)

let minimal_len_size (len: U64.t) : integer_size =
  (mk_raw_uint64 len).size

let minimal_len_size_prop (len: U64.t)
  : Lemma (raw_uint64_size_prop (minimal_len_size len) len)
= ()

(* ================================================================ *)
(* Ownership predicate                                              *)
(* ================================================================ *)

let cbor_array_owned (x: cbor_raw) (l: list raw_data_item) : slprop =
  exists* (xh: raw_data_item).
    cbor_raw_match 1.0R x xh **
    pure (Array? xh /\ Array?.v xh == l /\
          (Array?.len xh <: raw_uint64) == mk_raw_uint64 (FStar.UInt64.uint_to_t (List.Tot.length l)) /\
          CBOR_Case_Array? x /\ (CBOR_Case_Array?.v x).cbor_array_slice_perm == 1.0R)

(* ================================================================ *)
(* gather for cbor_raw_match (needed by singleton)                  *)
(* ================================================================ *)

ghost
fn cbor_raw_match_gather_aux
  (x1: cbor_raw) (#pm0: perm) (#x2: raw_data_item) (#pm0': perm) (#x2': raw_data_item)
requires cbor_raw_match pm0 x1 x2 ** cbor_raw_match pm0' x1 x2'
ensures cbor_raw_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
{
  cbor_raw_match_gather x1 #pm0 #x2 #pm0' #x2'
}

(* ================================================================ *)
(* Destructor: cbor_array_owned -> mixed_list at ambient 1.0R       *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

ghost
fn cbor_array_owned_to_ml
  (x: cbor_raw) (ml: IT.mixed_list cbor_raw) (l: Ghost.erased (list raw_data_item))
requires
  cbor_array_owned x l **
  pure (CBOR_Case_Array? x /\
        ((CBOR_Case_Array?.v x).cbor_array_ptr <: IT.mixed_list cbor_raw) == ml)
ensures
  I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml (Ghost.reveal l) **
  Trade.trade
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml (Ghost.reveal l))
    (cbor_array_owned x l) **
  pure (FStar.UInt.fits (SZ.v (IT.mixed_list_length ml)) 64)
{
  unfold (cbor_array_owned x l);
  with xh. assert (cbor_raw_match 1.0R x xh);
  cbor_raw_match_unfold_aux x;
  Access.cbor_raw_match_aux_cases cbor_raw_match 1.0R x;
  Access.cbor_raw_match_cases_prop_array_elim x (Ghost.reveal xh) () ();
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
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  Access.synth_array_major_type (Ghost.reveal xh) ();
  Access.content_array_list (Ghost.reveal xh) ();
  match x {
    CBOR_Case_Array v -> {
      Access.cbor_raw_get_array_content cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      with pm' cl. assert (
        I.mixed_list_match cbor_raw_match parse_raw_data_item pm' v.cbor_array_ptr cl **
        Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' v.cbor_array_ptr cl)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))));
      assert (pure (pm' == 1.0R));
      rewrite
        (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' v.cbor_array_ptr cl)
        as
        (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l));
      rewrite
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item pm' v.cbor_array_ptr cl)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))))
        as
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))));
      Trade.intro_trade
        (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
        (cbor_array_owned x l)
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))))
        fn _ {
          Trade.elim
            (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
              (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
              (CBOR_Case_Array v)
              (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))));
          Make.cbor_raw_match_fold_from_content_array 1.0R (CBOR_Case_Array v) (Ghost.reveal xh) ();
          rewrite (cbor_raw_match 1.0R (CBOR_Case_Array v) (Ghost.reveal xh))
            as (cbor_raw_match 1.0R x (Ghost.reveal xh));
          fold (cbor_array_owned x l);
        };
      rewrite
        (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
        as
        (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml (Ghost.reveal l));
      rewrite
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
          (cbor_array_owned x l))
        as
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml (Ghost.reveal l))
          (cbor_array_owned x l));
    }
    CBOR_Case_Invalid -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        CBOR_Case_Invalid
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Int i -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Int i)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Simple sv)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_String s -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_String s)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Map m -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Map m)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Tagged t)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      Access.cbor_raw_get_array_content_false cbor_raw_match 1.0R
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Tagged_Serialized ts)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
  }
}

#pop-options

(* ================================================================ *)
(* Non-ghost destructor: cbor_array_owned -> concrete mixed_list    *)
(* ================================================================ *)

ghost
fn cbor_array_owned_is_array
  (x: cbor_raw) (l: Ghost.erased (list raw_data_item))
requires cbor_array_owned x l
ensures cbor_array_owned x l ** pure (CBOR_Case_Array? x)
{
  unfold (cbor_array_owned x l);
  with xh. assert (cbor_raw_match 1.0R x xh);
  fold (cbor_array_owned x l);
}

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

fn cbor_array_owned_elim
  (x: cbor_raw) (l: Ghost.erased (list raw_data_item))
requires cbor_array_owned x l
returns ml: IT.mixed_list cbor_raw
ensures
  I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml (Ghost.reveal l) **
  Trade.trade
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml (Ghost.reveal l))
    (cbor_array_owned x l) **
  pure (CBOR_Case_Array? x /\
        ml == ((CBOR_Case_Array?.v x).cbor_array_ptr <: IT.mixed_list cbor_raw) /\
        FStar.UInt.fits (SZ.v (IT.mixed_list_length ml)) 64)
{
  cbor_array_owned_is_array x l;
  match x {
    CBOR_Case_Array v -> {
      cbor_array_owned_to_ml (CBOR_Case_Array v) v.cbor_array_ptr l;
      rewrite
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
          (cbor_array_owned (CBOR_Case_Array v) l))
        as
        (Trade.trade
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R v.cbor_array_ptr (Ghost.reveal l))
          (cbor_array_owned x l));
      v.cbor_array_ptr
    }
    CBOR_Case_Invalid -> { unreachable () }
    CBOR_Case_Int i -> { unreachable () }
    CBOR_Case_Simple sv -> { unreachable () }
    CBOR_Case_String s -> { unreachable () }
    CBOR_Case_Map m -> { unreachable () }
    CBOR_Case_Tagged t -> { unreachable () }
    CBOR_Case_Tagged_Serialized ts -> { unreachable () }
  }
}

(* The length of an owned array fits in a u64. Additive lemma used by the
   bridges (and ultimately by callers) to discharge the [fits] refinement that
   [finalize] requires after a chain of [append]s. *)
ghost
fn cbor_array_owned_length_fits
  (x: cbor_raw) (#l: Ghost.erased (list raw_data_item))
requires cbor_array_owned x l
ensures cbor_array_owned x l ** pure (FStar.UInt.fits (List.Tot.length (Ghost.reveal l)) 64)
{
  unfold (cbor_array_owned x l);
  with xh. assert (cbor_raw_match 1.0R x xh);
  fold (cbor_array_owned x l);
}

#pop-options

(* ================================================================ *)
(* Constructor: mixed_list -> cbor_array_owned (+ trade back)       *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

fn cbor_mk_array_full
  (f64: squash SZ.fits_u64)
  (len_size: integer_size)
  (ml: IT.mixed_list cbor_raw)
  (#l: Ghost.erased (list raw_data_item))
requires
  I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml l **
  pure (
    let len = SZ.v (IT.mixed_list_length ml) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop len_size (U64.uint_to_t len) /\
    len_size == minimal_len_size (U64.uint_to_t len) /\
    List.Tot.length l == len
  )
returns res: cbor_raw
ensures
  cbor_array_owned res l **
  Trade.trade
    (cbor_array_owned res l)
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml l)
{
  let the_prop =
    (let len = SZ.v (IT.mixed_list_length ml) in
     FStar.UInt.fits len 64 /\
     raw_uint64_size_prop len_size (U64.uint_to_t len) /\
     len_size == minimal_len_size (U64.uint_to_t len) /\
     List.Tot.length l == len);
  let sq = elim_pure_explicit the_prop;
  let len_sz = IT.mixed_list_length ml;
  let len64 = SZ.sizet_to_uint64 len_sz;
  let ru : raw_uint64 = { size = len_size; value = len64 };
  let v : cbor_array cbor_raw = {
    cbor_array_length_size = len_size;
    cbor_array_ptr = ml;
    cbor_array_slice_perm = 1.0R;
  };
  let res = CBOR_Case_Array v;
  let xh : Ghost.erased raw_data_item = Array ru l;
  cbor_raw_match_content_eq_array cbor_raw_match parse_raw_data_item 1.0R
    (dfst (dfst (synth_raw_data_item_recip xh)))
    (dsnd (dfst (synth_raw_data_item_recip xh)))
    v
    (dsnd (synth_raw_data_item_recip xh));
  rewrite
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml l)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item 1.0R
       (dfst (synth_raw_data_item_recip xh)) res (dsnd (synth_raw_data_item_recip xh)));
  Make.cbor_raw_match_fold_from_content_array 1.0R res xh ();
  assert (pure (U64.v len64 == SZ.v len_sz));
  assert (pure (len64 == U64.uint_to_t (List.Tot.length l)));
  assert (pure ((mk_raw_uint64 len64).value == len64));
  assert (pure (ru == mk_raw_uint64 (U64.uint_to_t (List.Tot.length l))));
  fold (cbor_array_owned res l);
  Trade.intro_trade
    (cbor_array_owned res l)
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml l)
    emp
    fn _ {
      cbor_array_owned_to_ml res ml l;
      drop_ (Trade.trade
        (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml l)
        (cbor_array_owned res l));
    };
  res
}

#pop-options

(* ================================================================ *)
(* Empty array                                                      *)
(* ================================================================ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_array_empty (_: unit)
requires emp
returns res: cbor_raw
ensures cbor_array_owned res []
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  Append.mixed_list_empty cbor_raw_match parse_raw_data_item 1.0R;
  let ml : IT.mixed_list cbor_raw = IT.Base IT.Empty;
  rewrite (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R (IT.Base (IT.Empty #cbor_raw)) [])
    as (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml []);
  let len_size = minimal_len_size 0uL;
  minimal_len_size_prop 0uL;
  let res = cbor_mk_array_full f64 len_size ml #[];
  drop_ (Trade.trade
    (cbor_array_owned res [])
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml []));
  res
}

#pop-options

(* ================================================================ *)
(* Singleton array                                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_array_singleton
  (x: cbor_raw) (ry: R.ref cbor_raw)
  (#pm: perm) (#v: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm x v ** (exists* w. R.pts_to ry w)
returns res: cbor_raw
ensures
  cbor_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_array_owned res [Ghost.reveal v])
    (cbor_raw_match pm x v ** (exists* w. R.pts_to ry w))
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let ml = Append.mixed_list_singleton cbor_raw_match parse_raw_data_item
    pm x v ry cbor_raw_match_gather_aux;
  let len_size = minimal_len_size 1uL;
  minimal_len_size_prop 1uL;
  let res = cbor_mk_array_full f64 len_size ml #[Ghost.reveal v];
  Trade.trans
    (cbor_array_owned res [Ghost.reveal v])
    (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml [Ghost.reveal v])
    (cbor_raw_match pm x v ** (exists* w. R.pts_to ry w));
  res
}

#pop-options

(* ================================================================ *)
(* Append of two arrays                                             *)
(* ================================================================ *)

(* The overflow check [U64.gt la (0xffffffffffffffff - lb)] taken in the
   failure branch of [cbor_array_append] witnesses that the sum of the two
   lengths does not fit in a u64. We phrase this over the (possibly truncated)
   u64 views [la = na % 2^64] and [lb = nb % 2^64] of the underlying nat
   lengths so that the conclusion holds without assuming the size_t values
   themselves are below 2^64. *)
let array_append_overflow (la lb: U64.t) (na nb: nat)
: Lemma
    (requires
      U64.v la > U64.v (U64.sub 0xffffffffffffffffuL lb) /\
      U64.v la == na % pow2 64 /\
      U64.v lb == nb % pow2 64)
    (ensures ~ (FStar.UInt.fits (na + nb) U64.n))
= FStar.Math.Lemmas.lemma_mod_lt na (pow2 64);
  FStar.Math.Lemmas.lemma_mod_lt nb (pow2 64);
  assert_norm (pow2 64 == 0xffffffffffffffff + 1)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_array_append
  (x1 x2: cbor_raw)
  (r_before r_after: R.ref (IT.mixed_list cbor_raw))
  (#l1 #l2: Ghost.erased (list raw_data_item))
requires
  cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
  (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)
returns res: option cbor_raw
ensures
  (match res with
   | None ->
     cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
     pure (~ (FStar.UInt.fits (List.Tot.length (Ghost.reveal l1) + List.Tot.length (Ghost.reveal l2)) U64.n))
   | Some r ->
     cbor_array_owned r (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_array_owned r (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let ml_a = cbor_array_owned_elim x1 l1;
  let ml_b = cbor_array_owned_elim x2 l2;
  I.mixed_list_match_length cbor_raw_match parse_raw_data_item 1.0R ml_a l1;
  I.mixed_list_match_length cbor_raw_match parse_raw_data_item 1.0R ml_b l2;
  let len_a = IT.mixed_list_length ml_a;
  let len_b = IT.mixed_list_length ml_b;
  let la64 = SZ.sizet_to_uint64 len_a;
  let lb64 = SZ.sizet_to_uint64 len_b;
  let limit = U64.sub 0xffffffffffffffffuL lb64;
  if U64.gt la64 limit {
    // sum would not fit in u64: restore both owned predicates, return None
    array_append_overflow la64 lb64 (SZ.v len_a) (SZ.v len_b);
    Trade.elim
      (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_a (Ghost.reveal l1))
      (cbor_array_owned x1 l1);
    Trade.elim
      (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_b (Ghost.reveal l2))
      (cbor_array_owned x2 l2);
    None #cbor_raw
  } else {
    let sum64 = U64.add la64 lb64;
    SZ.fits_u64_implies_fits (SZ.v len_a + SZ.v len_b);
    let ml_res = Append.mixed_list_append cbor_raw_match parse_raw_data_item 1.0R
      ml_a l1 ml_b l2 r_before r_after;
    List.Tot.Properties.append_length (Ghost.reveal l1) (Ghost.reveal l2);
    let len_size = minimal_len_size sum64;
    minimal_len_size_prop sum64;
    let res = cbor_mk_array_full f64 len_size ml_res
      #(List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2));
    Trade.intro_trade
      (cbor_array_owned res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
      (cbor_array_owned x1 l1 ** cbor_array_owned x2 l2 **
       (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
      (Trade.trade
         (cbor_array_owned res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
         (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2))) **
       Trade.trade
         (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
         (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_a l1 **
          I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_b l2 **
          (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)) **
       Trade.trade
         (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_a l1)
         (cbor_array_owned x1 l1) **
       Trade.trade
         (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_b l2)
         (cbor_array_owned x2 l2))
      fn _ {
        Trade.elim
          (cbor_array_owned res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)));
        Trade.elim
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_res (List.Tot.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_a l1 **
           I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_b l2 **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va));
        Trade.elim
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_a l1)
          (cbor_array_owned x1 l1);
        Trade.elim
          (I.mixed_list_match cbor_raw_match parse_raw_data_item 1.0R ml_b l2)
          (cbor_array_owned x2 l2);
      };
    Some #cbor_raw res
  }
}

#pop-options
