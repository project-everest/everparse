module CBOR.Pulse.Raw.Nondet.Alloc
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base

module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZCmp = CBOR.Pulse.Raw.EverParse.SizeComparison
module CA = CBOR.Pulse.API.Nondet.C.Alloc
module RA = CBOR.Pulse.API.Nondet.Rust.Alloc
module Nondet = CBOR.Pulse.Raw.Nondet

(* Verified wrappers around the bounded sort- and hash-based validators,
   which allocate their scratch spaces on the heap once per call, using
   the trusted allocators of CBOR.Pulse.API.Nondet.{C,Rust}.Alloc, and
   free them before returning. *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn sizet_to_u64 (x: SZ.t)
  requires emp
  returns res: option U64.t
  ensures pure (Some? res ==> U64.v (Some?.v res) == SZ.v x)
{
  let ok = SZCmp.sizet_fits_u64 x;
  if ok {
    FStar.Math.Lemmas.small_mod (SZ.v x) (pow2 64);
    Some (SZ.sizet_to_uint64 x)
  } else {
    None #U64.t
  }
}

let mul_div_le (n k m: nat) : Lemma
  (requires k > 0 /\ n <= m / k)
  (ensures n * k <= m)
= FStar.Math.Lemmas.lemma_mult_le_right k n (m / k);
  FStar.Math.Lemmas.lemma_div_mod m k

(* 3 * map_length_bound * map_depth_bound (+ map_length_bound if extra),
   or None if it does not fit U64.t *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn scratch_count (map_depth_bound map_length_bound: SZ.t) (extra: bool)
  requires emp
  returns res: option U64.t
  ensures pure (Some? res ==> U64.v (Some?.v res) == 3 * SZ.v map_length_bound * SZ.v map_depth_bound + (if extra then SZ.v map_length_bound else 0))
{
  let od = sizet_to_u64 map_depth_bound;
  let on = sizet_to_u64 map_length_bound;
  match od {
    None -> { None #U64.t }
    Some d -> {
      match on {
        None -> { None #U64.t }
        Some n -> {
          if (U64.gt d 0x5555555555555554uL) {
            None #U64.t
          } else {
            let k = U64.add (U64.mul 3uL d) (if extra then 1uL else 0uL);
            if (k = 0uL) {
              Some 0uL
            } else if (U64.gt n (U64.div 0xFFFFFFFFFFFFFFFFuL k)) {
              None #U64.t
            } else {
              mul_div_le (U64.v n) (U64.v k) 0xFFFFFFFFFFFFFFFF;
              Some (U64.mul n k)
            }
          }
        }
      }
    }
  }
}

(* C: the trusted allocators return possibly-NULL pointers *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_validate_bounded_sort_alloc_c
  (validate: cbor_nondet_validate_bounded_sort_t)
: cbor_nondet_validate_bounded_sort_alloc_t
=
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let oc = scratch_count map_depth_bound map_length_bound false;
  match oc {
    None -> { 0sz }
    Some c -> {
      let p = CA.cbor_nondet_malloc_size_t c;
      unfold (CA.cbor_nondet_malloc_post CA.cbor_nondet_freeable_size_t c p);
      with vp . assert (AP.pts_to_or_null p vp);
      let isnull = AP.is_null p;
      if (isnull) {
        rewrite (AP.pts_to_or_null p vp) as emp;
        drop_ (CA.cbor_nondet_freeable_size_t p);
        0sz
      } else {
        rewrite (AP.pts_to_or_null p vp) as (AP.pts_to p vp);
        let sc = S.arrayptr_to_slice_intro p (SZ.uint64_to_sizet c);
        let res = validate map_depth_bound map_length_bound map_key_bound sc input;
        S.arrayptr_to_slice_elim sc;
        CA.cbor_nondet_free_size_t p;
        res
      }
    }
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_validate_bounded_hash_alloc_c
  (validate: cbor_nondet_validate_bounded_hash_t)
: cbor_nondet_validate_bounded_hash_alloc_t
=
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (k0: U64.t)
  (k1: U64.t)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let oc = scratch_count map_depth_bound map_length_bound true;
  let ohc = sizet_to_u64 map_length_bound;
  match oc {
    None -> { 0sz }
    Some c -> {
      match ohc {
        None -> { 0sz }
        Some hc -> {
          let p = CA.cbor_nondet_malloc_size_t c;
          unfold (CA.cbor_nondet_malloc_post CA.cbor_nondet_freeable_size_t c p);
          with vp . assert (AP.pts_to_or_null p vp);
          let isnull = AP.is_null p;
          if (isnull) {
            rewrite (AP.pts_to_or_null p vp) as emp;
            drop_ (CA.cbor_nondet_freeable_size_t p);
            0sz
          } else {
            rewrite (AP.pts_to_or_null p vp) as (AP.pts_to p vp);
            let hp = CA.cbor_nondet_malloc_uint64_t hc;
            unfold (CA.cbor_nondet_malloc_post CA.cbor_nondet_freeable_uint64_t hc hp);
            with vhp . assert (AP.pts_to_or_null hp vhp);
            let hisnull = AP.is_null hp;
            if (hisnull) {
              rewrite (AP.pts_to_or_null hp vhp) as emp;
              drop_ (CA.cbor_nondet_freeable_uint64_t hp);
              CA.cbor_nondet_free_size_t p;
              0sz
            } else {
              rewrite (AP.pts_to_or_null hp vhp) as (AP.pts_to hp vhp);
              let sc = S.arrayptr_to_slice_intro p (SZ.uint64_to_sizet c);
              let hsc = S.arrayptr_to_slice_intro hp (SZ.uint64_to_sizet hc);
              let res = validate map_depth_bound map_length_bound map_key_bound k0 k1 sc hsc input;
              S.arrayptr_to_slice_elim hsc;
              S.arrayptr_to_slice_elim sc;
              CA.cbor_nondet_free_uint64_t hp;
              CA.cbor_nondet_free_size_t p;
              res
            }
          }
        }
      }
    }
  }
}

(* Rust: the trusted allocators return optional slices *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_validate_bounded_sort_alloc_rust
  (validate: cbor_nondet_validate_bounded_sort_t)
: cbor_nondet_validate_bounded_sort_alloc_t
=
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let oc = scratch_count map_depth_bound map_length_bound false;
  match oc {
    None -> { 0sz }
    Some c -> {
      let osc = RA.cbor_nondet_alloc_usize c;
      match osc {
        None -> {
          unfold (RA.cbor_nondet_alloc_post RA.cbor_nondet_freeable_usize c None);
          0sz
        }
        Some sc -> {
          unfold (RA.cbor_nondet_alloc_post RA.cbor_nondet_freeable_usize c (Some sc));
          let res = validate map_depth_bound map_length_bound map_key_bound sc input;
          RA.cbor_nondet_free_usize sc;
          res
        }
      }
    }
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_validate_bounded_hash_alloc_rust
  (validate: cbor_nondet_validate_bounded_hash_t)
: cbor_nondet_validate_bounded_hash_alloc_t
=
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (k0: U64.t)
  (k1: U64.t)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let oc = scratch_count map_depth_bound map_length_bound true;
  let ohc = sizet_to_u64 map_length_bound;
  match oc {
    None -> { 0sz }
    Some c -> {
      match ohc {
        None -> { 0sz }
        Some hc -> {
          let osc = RA.cbor_nondet_alloc_usize c;
          match osc {
            None -> {
              unfold (RA.cbor_nondet_alloc_post RA.cbor_nondet_freeable_usize c None);
              0sz
            }
            Some sc -> {
              unfold (RA.cbor_nondet_alloc_post RA.cbor_nondet_freeable_usize c (Some sc));
              let ohsc = RA.cbor_nondet_alloc_u64 hc;
              match ohsc {
                None -> {
                  unfold (RA.cbor_nondet_alloc_post RA.cbor_nondet_freeable_u64 hc None);
                  RA.cbor_nondet_free_usize sc;
                  0sz
                }
                Some hsc -> {
                  unfold (RA.cbor_nondet_alloc_post RA.cbor_nondet_freeable_u64 hc (Some hsc));
                  let res = validate map_depth_bound map_length_bound map_key_bound k0 k1 sc hsc input;
                  RA.cbor_nondet_free_u64 hsc;
                  RA.cbor_nondet_free_usize sc;
                  res
                }
              }
            }
          }
        }
      }
    }
  }
}

