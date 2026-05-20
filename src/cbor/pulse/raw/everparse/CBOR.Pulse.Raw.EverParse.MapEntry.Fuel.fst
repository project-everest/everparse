module CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Read
open CBOR.Pulse.Raw.EverParse.Validate
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator

// Shared infrastructure for fuel-aware map-entry vmatch, lifted out of
// Det.Compare so that both Det and Nondet comparators can reuse it without
// duplication.

// === Map-entry vmatch at fuel n ===
// cbor_map_entry_match with cbor_raw_match_fuel n as the child relation.
let cbor_map_entry_vmatch_fuel
  (n: nat)
  (pm: perm)
  (elem: cbor_map_entry cbor_raw)
  (v: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_map_entry_match (cbor_raw_match_fuel n) pm elem v

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn cbor_map_entry_vmatch_fuel_share_wrapper
  (n: nat)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch_fuel n pm entry pair
ensures cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair **
        cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair
{
  unfold (cbor_map_entry_vmatch_fuel n pm entry pair);
  cbor_map_entry_match_share (cbor_raw_match_fuel n) (cbor_raw_match_fuel_share_t n) entry;
  fold (cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair);
  fold (cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair);
}

ghost
fn cbor_map_entry_vmatch_fuel_gather_wrapper
  (n: nat)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm) (#pair: (raw_data_item & raw_data_item))
  (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch_fuel n pm entry pair **
         cbor_map_entry_vmatch_fuel n pm' entry pair'
ensures cbor_map_entry_vmatch_fuel n (pm +. pm') entry pair **
        pure (pair == pair')
{
  // Mirror NC.cbor_map_entry_vmatch_gather_wrapper: unfold everything by hand,
  // call cbor_raw_match_fuel_gather on key/value, then fold back.
  unfold (cbor_map_entry_vmatch_fuel n pm entry pair);
  unfold (cbor_map_entry_vmatch_fuel n pm' entry pair');
  unfold (cbor_map_entry_match (cbor_raw_match_fuel n) pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel n pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel n pm) cbor_map_entry_value_proj entry (snd pair));
  unfold (cbor_map_entry_match (cbor_raw_match_fuel n) pm' entry pair');
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel n pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n pm') cbor_map_entry_value_proj) entry pair');
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel n pm') cbor_map_entry_value_proj entry (snd pair'));
  rewrite (cbor_raw_match_fuel n pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match_fuel n pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match_fuel n pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair'))
       as (cbor_raw_match_fuel n pm' entry.cbor_map_entry_key (fst pair'));
  rewrite (cbor_raw_match_fuel n pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match_fuel n pm entry.cbor_map_entry_value (snd pair));
  rewrite (cbor_raw_match_fuel n pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair'))
       as (cbor_raw_match_fuel n pm' entry.cbor_map_entry_value (snd pair'));
  cbor_raw_match_fuel_gather n entry.cbor_map_entry_key
    #pm #(Ghost.hide (fst pair)) #pm' #(Ghost.hide (fst pair'));
  cbor_raw_match_fuel_gather n entry.cbor_map_entry_value
    #pm #(Ghost.hide (snd pair)) #pm' #(Ghost.hide (snd pair'));
  rewrite (cbor_raw_match_fuel n (pm +. pm') entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match_fuel n (pm +. pm') (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match_fuel n (pm +. pm') entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match_fuel n (pm +. pm') (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match_fuel n (pm +. pm')) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match_fuel n (pm +. pm')) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n (pm +. pm')) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match (cbor_raw_match_fuel n) (pm +. pm') entry pair);
  fold (cbor_map_entry_vmatch_fuel n (pm +. pm') entry pair);
}

let cbor_map_entry_vmatch_fuel_share_t (n: nat) : I.share_t (cbor_map_entry_vmatch_fuel n) =
  cbor_map_entry_vmatch_fuel_share_wrapper n

let cbor_map_entry_vmatch_fuel_gather_t (n: nat) : I.gather_t (cbor_map_entry_vmatch_fuel n) =
  cbor_map_entry_vmatch_fuel_gather_wrapper n

#pop-options

// Ghost helper to split a fuel map-entry vmatch into key + value matches.
ghost fn cbor_map_entry_vmatch_fuel_elim
  (m: nat)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch_fuel m pm entry pair
ensures
  cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)) **
  cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair))
{
  unfold (cbor_map_entry_vmatch_fuel m pm entry pair);
  unfold (cbor_map_entry_match (cbor_raw_match_fuel m) pm entry (Ghost.reveal pair));
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel m pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj) entry (Ghost.reveal pair));
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj entry (snd (Ghost.reveal pair)));
  rewrite (cbor_raw_match_fuel m pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)));
  rewrite (cbor_raw_match_fuel m pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair)));
}

// Ghost helper to fold key + value matches back into a fuel map-entry vmatch.
ghost fn cbor_map_entry_vmatch_fuel_intro
  (m: nat)
  (entry: cbor_map_entry cbor_raw)
  (pm: perm)
  (pair: Ghost.erased (raw_data_item & raw_data_item))
requires
  cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)) **
  cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair))
ensures cbor_map_entry_vmatch_fuel m pm entry pair
{
  rewrite (cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst (Ghost.reveal pair)));
  rewrite (cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd (Ghost.reveal pair)));
  fold (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj entry (snd (Ghost.reveal pair)));
  fold (vmatch_pair_with_proj (cbor_raw_match_fuel m pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj) entry (Ghost.reveal pair));
  fold (cbor_map_entry_match (cbor_raw_match_fuel m) pm entry (Ghost.reveal pair));
  fold (cbor_map_entry_vmatch_fuel m pm entry pair);
}

// Pair reader at fuel m. Mirrors NC.cbor_map_entry_zero_copy_parse but uses
// cbor_raw_read_fuel m pm0 instead of cbor_raw_read 1.0R, producing
// cbor_map_entry_vmatch_fuel m pm0 entry v in the postcondition.

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_map_entry_zero_copy_parse_fuel
  (m: Ghost.erased nat { Ghost.reveal m >= 1 })
  (pm0: perm)
  (f64: squash SZ.fits_u64)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry cbor_raw
ensures cbor_map_entry_vmatch_fuel (Ghost.reveal m) pm0 res v **
        Trade.trade (cbor_map_entry_vmatch_fuel (Ghost.reveal m) pm0 res v)
                    (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  let zcp1 = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read_fuel m pm0 f64) ();
  let pair = LowParse.PulseParse.Combinators.zero_copy_parse_nondep_then (jump_raw_data_item f64) zcp1 () zcp1 input;
  let entry : cbor_map_entry cbor_raw = { cbor_map_entry_key = fst pair; cbor_map_entry_value = snd pair };
  rewrite (vmatch_pair (cbor_raw_match_fuel (Ghost.reveal m) pm0) (cbor_raw_match_fuel (Ghost.reveal m) pm0) pair (Ghost.reveal v))
       as (cbor_map_entry_vmatch_fuel (Ghost.reveal m) pm0 entry v);
  rewrite (Trade.trade (vmatch_pair (cbor_raw_match_fuel (Ghost.reveal m) pm0) (cbor_raw_match_fuel (Ghost.reveal m) pm0) pair (Ghost.reveal v))
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v))
       as (Trade.trade (cbor_map_entry_vmatch_fuel (Ghost.reveal m) pm0 entry v)
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v));
  entry
}

#pop-options
