module CBOR.Pulse.Raw.EverParse.Det.Compare.Dispatch
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.TaggedCase
include CBOR.Pulse.Raw.EverParse.Det.Compare.ArrayCase
include CBOR.Pulse.Raw.EverParse.Det.Compare.MapCase
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module I16 = FStar.Int16
module IT = LowParse.PulseParse.Iterator.Type
module NC = CBOR.Pulse.Raw.EverParse.Nondet.Compare

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn cbor_compare_dispatch_body
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih_tagged: compare_cbor_raw_fuel_tagged_local_t n)
  (ih_array: compare_cbor_raw_fuel_array_local_t n)
  (ih_map: compare_cbor_raw_fuel_map_local_t n)
: compare_cbor_raw_fuel_t n
=
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
{
  // Unfold both fuel-matches to aux
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);

  // Derive cases / fields props on both sides
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm1 x1;
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm2 x2;
  NC.cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm1 x1;
  NC.cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm2 x2;

  // Read major types
  let ty1 = cbor_raw_get_major_type_aux (cbor_raw_match_fuel (n - 1)) pm1 x1;
  let ty2 = cbor_raw_get_major_type_aux (cbor_raw_match_fuel (n - 1)) pm2 x2;
  let c = impl_uint8_compare () ty1 ty2;

  if (c = 0s) {
    if (ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64) {
      let ru1 = cbor_raw_int_raw_uint64 x1;
      let ru2 = cbor_raw_int_raw_uint64 x2;
      cbor_raw_int_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_int_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let res = impl_raw_uint64_compare () ru1 ru2;
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      res
    } else if (ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string) {
      let len1 = cbor_raw_string_len x1;
      let len2 = cbor_raw_string_len x2;
      cbor_raw_string_len_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_string_len_eq x2 (Ghost.reveal v2) () ();
      let cl : I16.t = impl_raw_uint64_compare () len1 len2;
      if (cl = 0s) {
        let s1 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
        let s2 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
        let res = lex_compare_bytes s1 s2;
        Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
        Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        res
      } else {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        cl
      }
    } else if (ty1 = cbor_major_type_tagged) {
      let tag1 = cbor_raw_tag_raw_uint64 x1;
      let tag2 = cbor_raw_tag_raw_uint64 x2;
      cbor_raw_tag_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_tag_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let ct = impl_raw_uint64_compare () tag1 tag2;
      if (ct = 0s) {
        // Refold to cbor_raw_match_fuel n, then delegate to the tagged callback.
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        ih_tagged () x1 x2 #pm1 #v1 #pm2 #v2
      } else {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        ct
      }
    } else if (ty1 = cbor_major_type_array) {
      let len1 = cbor_raw_array_raw_uint64 x1;
      let len2 = cbor_raw_array_raw_uint64 x2;
      cbor_raw_array_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_array_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let cl = impl_raw_uint64_compare () len1 len2;
      if (cl = 0s) {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        let len_sz = SZ.uint64_to_sizet len1.value;
        ih_array () x1 x2 len_sz () #pm1 #v1 #pm2 #v2
      } else {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        cl
      }
    } else if (ty1 = cbor_major_type_map) {
      let len1 = cbor_raw_map_raw_uint64 x1;
      let len2 = cbor_raw_map_raw_uint64 x2;
      cbor_raw_map_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_map_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let cl = impl_raw_uint64_compare () len1 len2;
      if (cl = 0s) {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        let len_sz = SZ.uint64_to_sizet len1.value;
        ih_map () x1 x2 len_sz () #pm1 #v1 #pm2 #v2
      } else {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        cl
      }
    } else {
      // Simple value
      let sv1 = CBOR_Case_Simple?.v x1;
      let sv2 = CBOR_Case_Simple?.v x2;
      let res = impl_uint8_compare () sv1 sv2;
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      res
    }
  } else {
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    c
  }
}
```

#pop-options

// Pulse wrapper that derives n >= 1 from slprop and invokes the dispatcher.
// `inline_for_extraction` so its body inlines into impl_cbor_compare_fuel.

inline_for_extraction
```pulse
fn impl_cbor_compare_fuel_top
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (ih_tagged: compare_cbor_raw_fuel_tagged_local_t n)
  (ih_array: compare_cbor_raw_fuel_array_local_t n)
  (ih_map: compare_cbor_raw_fuel_map_local_t n)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
  cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2
returns res: I16.t
ensures
  cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
  cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  cbor_raw_match_fuel_implies_pos (Ghost.reveal n) x1 #pm1 #v1;
  // Now Ghost.reveal n >= 1 in slprop; Pulse can discharge the refinement
  // on n required by dispatch_body.
  cbor_compare_dispatch_body f64 n ih_tagged ih_array ih_map x1 x2 #pm1 #v1 #pm2 #v2
}
```
