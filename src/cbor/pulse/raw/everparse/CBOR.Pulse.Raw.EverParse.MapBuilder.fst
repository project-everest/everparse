module CBOR.Pulse.Raw.EverParse.MapBuilder
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

(* ================================================================ *)
(* Function 2: rebuild  -- perm-polymorphic fractional mk_map       *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

fn cbor_mk_map_full
  (f64: squash SZ.fits_u64)
  (pm: perm)
  (len_size: integer_size)
  (ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  pure (let len = SZ.v (IT.mixed_list_length ml) in
        FStar.UInt.fits len 64 /\
        raw_uint64_size_prop len_size (U64.uint_to_t len) /\
        List.Tot.length l == len)
returns res: cbor_raw
ensures exists* (xh: raw_data_item).
  cbor_raw_match pm res xh **
  Trade.trade (cbor_raw_match pm res xh)
    (I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l) **
  pure (Map? xh /\ (Map?.v xh <: list (raw_data_item & raw_data_item)) == Ghost.reveal l /\
        (Map?.len xh).size == len_size /\ (Map?.len xh).value == U64.uint_to_t (List.Tot.length l) /\
        (CBOR_Case_Map? res /\ ((CBOR_Case_Map?.v res).cbor_map_ptr <: IT.mixed_list (cbor_map_entry cbor_raw)) == ml /\
         (CBOR_Case_Map?.v res).cbor_map_slice_perm == 1.0R))
{
  let the_prop =
    (let len = SZ.v (IT.mixed_list_length ml) in
     FStar.UInt.fits len 64 /\
     raw_uint64_size_prop len_size (U64.uint_to_t len) /\
     List.Tot.length l == len);
  let sq = elim_pure_explicit the_prop;
  let len_sz = IT.mixed_list_length ml;
  let len64 = SZ.sizet_to_uint64 len_sz;
  assert (pure (U64.v len64 == List.Tot.length l));
  assert (pure (len64 == U64.uint_to_t (List.Tot.length l)));
  let ru : raw_uint64 = { size = len_size; value = len64 };
  let v : cbor_map cbor_raw = {
    cbor_map_length_size = len_size;
    cbor_map_ptr = ml;
    cbor_map_slice_perm = 1.0R;
  };
  let res = CBOR_Case_Map v;
  let xh : Ghost.erased raw_data_item = Map ru l;
  rewrite
    (I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    as
    (I.mixed_list_match
       (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm' elem x)
       (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
  cbor_raw_match_content_eq_map cbor_raw_match parse_raw_data_item pm
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
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
       (dfst (synth_raw_data_item_recip xh)) res (dsnd (synth_raw_data_item_recip xh)));
  Make.cbor_raw_match_fold_from_content_map pm res xh ();
  Trade.intro_trade
    (cbor_raw_match pm res xh)
    (I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    emp
    fn _ {
      rewrite (cbor_raw_match pm res (Ghost.reveal xh))
        as (cbor_raw_match pm (CBOR_Case_Map v) (Ghost.reveal xh));
      let x : cbor_raw = CBOR_Case_Map v;
      rewrite (cbor_raw_match pm (CBOR_Case_Map v) (Ghost.reveal xh))
        as (cbor_raw_match pm x (Ghost.reveal xh));
      cbor_raw_match_unfold_aux x;
      unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal xh));
      unfold (vmatch_synth
        (vmatch_dep_pair_with_proj
           cbor_raw_match_header
           cbor_raw_id_proj
           (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
        synth_raw_data_item_recip
        x (Ghost.reveal xh));
      unfold (vmatch_dep_pair_with_proj
        cbor_raw_match_header
        cbor_raw_id_proj
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
        x
        (synth_raw_data_item_recip (Ghost.reveal xh)));
      unfold (cbor_raw_match_header
        (cbor_raw_id_proj.pair_proj_get x)
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
      drop_ (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
             Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
      cbor_raw_match_content_eq_map cbor_raw_match parse_raw_data_item pm
        (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
        (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)));
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
          x
          (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
        as
        (I.mixed_list_match
           (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm' elem x)
           (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
      rewrite
        (I.mixed_list_match
           (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm' elem x)
           (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
        as
        (I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
    };
  res
}

#pop-options

(* ================================================================ *)
(* Function 1: borrow  -- ghost, perm-polymorphic                   *)
(* ================================================================ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

ghost
fn cbor_map_borrow_entries
  (pm: perm) (x: cbor_raw) (xh: Ghost.erased raw_data_item)
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  cbor_raw_match pm x xh **
  pure (Map? xh /\ (Map?.v xh <: list (raw_data_item & raw_data_item)) == Ghost.reveal l)
ensures exists* (pm': perm) (ml: IT.mixed_list (cbor_map_entry cbor_raw)).
  I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml (Ghost.reveal l) **
  Trade.trade
    (I.mixed_list_match (cbor_map_entry_match cbor_raw_match) (nondep_then parse_raw_data_item parse_raw_data_item) pm' ml (Ghost.reveal l))
    (cbor_raw_match pm x xh) **
  pure (CBOR_Case_Map? x /\
        ml == ((CBOR_Case_Map?.v x).cbor_map_ptr <: IT.mixed_list (cbor_map_entry cbor_raw)) /\
        pm' == pm *. (CBOR_Case_Map?.v x).cbor_map_slice_perm /\
        FStar.UInt.fits (SZ.v (IT.mixed_list_length ml)) 64)
{
  cbor_raw_match_unfold_aux x;
  Access.cbor_raw_match_aux_cases cbor_raw_match pm x;
  Access.cbor_raw_match_cases_prop_map_elim x (Ghost.reveal xh) () ();
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal xh));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
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
  Access.synth_map_major_type (Ghost.reveal xh) ();
  Access.content_map_list (Ghost.reveal xh) ();
  match x {
    CBOR_Case_Map v -> {
      Access.cbor_raw_get_map_content cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      with pm' cl. assert (
        I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr cl **
        Trade.trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr cl)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))));
      Access.content_map_list (Ghost.reveal xh) ();
      (* change cl -> l (same lambda vmatch; SMT proves cl == l) *)
      rewrite
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr cl)
        as
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l));
      rewrite
        (Trade.trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr cl)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))))
        as
        (Trade.trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))));
      (* build the trade back to cbor_raw_match (still in lambda form) *)
      Trade.intro_trade
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
        (cbor_raw_match pm x (Ghost.reveal xh))
        (Trade.trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))))
        fn _ {
          Trade.elim
            (I.mixed_list_match
              (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
                cbor_map_entry_match cbor_raw_match pm0 elem vi)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
              (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
              (CBOR_Case_Map v)
              (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))));
          Make.cbor_raw_match_fold_from_content_map pm (CBOR_Case_Map v) (Ghost.reveal xh) ();
          rewrite (cbor_raw_match pm (CBOR_Case_Map v) (Ghost.reveal xh))
            as (cbor_raw_match pm x (Ghost.reveal xh));
        };
      (* convert lambda vmatch -> named vmatch (eta only) *)
      rewrite
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
        as
        (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l));
      rewrite
        (Trade.trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
          (cbor_raw_match pm x (Ghost.reveal xh)))
        as
        (Trade.trade
          (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm' v.cbor_map_ptr (Ghost.reveal l))
          (cbor_raw_match pm x (Ghost.reveal xh)));
    }
    CBOR_Case_Invalid -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        CBOR_Case_Invalid
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Int i -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Int i)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Simple sv)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_String s -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_String s)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Array a -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Array a)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Tagged t)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      Access.cbor_raw_get_map_content_false cbor_raw_match pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_Tagged_Serialized ts)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
        ();
      unreachable ()
    }
  }
}

#pop-options
