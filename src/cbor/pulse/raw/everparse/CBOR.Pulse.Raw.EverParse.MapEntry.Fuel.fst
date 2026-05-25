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
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference

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
  let pair = LowParse.PulseParse.Combinators.zero_copy_parse_nondep_then jump_raw_data_item_eta zcp1 () zcp1 input;
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

(* ====================================================================
   Non-inline specializations of iterator_next for the two fuel-vmatch
   + parser combinations used by Nondet.Compare's comparators when
   advancing iterators of cbor_raw or cbor_map_entry cbor_raw values.
   The bodies inline iterator_next once, baking in jumper and
   zero-copy parser. Callers therefore only need to provide pm, r,
   i_orig, l — no zcp / jumper passed at runtime, which both keeps
   karamel from emitting partial-application warnings and prevents
   iterator_next's body from being inlined into a (potentially
   recursive) comparator, where it would inflate the stack frame.
==================================================================== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_raw_data_item_fuel
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (f64: squash SZ.fits_u64)
  (pm: perm)
  (x: IT.iterator cbor_raw)
  (l: Ghost.erased (list raw_data_item))
requires
  I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm
    x (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: (cbor_raw & IT.iterator cbor_raw)
ensures
  (exists* pm_v hd_val tl_l pm' .
    cbor_raw_match_fuel (Ghost.reveal n) pm_v (fst res) hd_val **
    I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm'
      (snd res) tl_l **
    Trade.trade
      (cbor_raw_match_fuel (Ghost.reveal n) pm_v (fst res) hd_val **
       I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm'
         (snd res) tl_l)
      (I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm
         x (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let zcp = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read_fuel n 1.0R f64) ();
  let mut r = x;
  let elt = I.iterator_next
    (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    jump_raw_data_item_eta
    pm r _ l
    (cbor_raw_match_fuel_share_t (Ghost.reveal n))
    (cbor_raw_match_fuel_gather_t (Ghost.reveal n))
    zcp;
  unfold (I.iterator_next_post (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    pm r x (Ghost.reveal l) elt);
  let x' = !r;
  (elt, x')
}
```

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_map_entry_raw_data_item_fuel
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (f64: squash SZ.fits_u64)
  (pm: perm)
  (x: IT.iterator (cbor_map_entry cbor_raw))
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.iterator_match
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm x (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: (cbor_map_entry cbor_raw & IT.iterator (cbor_map_entry cbor_raw))
ensures
  (exists* pm_v hd_val tl_l pm' .
    cbor_map_entry_vmatch_fuel (Ghost.reveal n) pm_v (fst res) hd_val **
    I.iterator_match
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' (snd res) tl_l **
    Trade.trade
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n) pm_v (fst res) hd_val **
       I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm' (snd res) tl_l)
      (I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm x (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let zcp = cbor_map_entry_zero_copy_parse_fuel n 1.0R f64;
  let mut r = x;
  let elt = I.iterator_next
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    jump_nondep_then_raw_data_item_eta
    pm r _ l
    (cbor_map_entry_vmatch_fuel_share_t (Ghost.reveal n))
    (cbor_map_entry_vmatch_fuel_gather_t (Ghost.reveal n))
    zcp;
  unfold (I.iterator_next_post
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm r x (Ghost.reveal l) elt);
  let x' = !r;
  (elt, x')
}
```

#pop-options

(* ====================================================================
   Non-inline by-value wrappers around iterator_start, specialized to
   the two fuel-vmatch + parser combinations used by Det.Compare /
   Nondet.Compare. By NOT being inline_for_extraction, the wrapper
   absorbs all of iterator_start's working set (mixed_list traversal
   loop, base-mixed-list narrow, share trades) into its own stack frame
   rather than expanding the recursive comparator's frame.

   The wrapper takes the mixed_list by value and returns the iterator
   by value, mirroring the existing iterator_next_*_fuel byval wrappers.
==================================================================== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_start_raw_data_item_fuel
  (n: Ghost.erased nat)
  (pm: perm)
  (ml: IT.mixed_list cbor_raw)
  (l: Ghost.erased (list raw_data_item))
requires
  I.mixed_list_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm ml l
returns it: IT.iterator cbor_raw
ensures
  (exists* pm'.
    I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm' it l **
    Trade.trade
      (I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm' it l)
      (I.mixed_list_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm ml l))
{
  let it = I.iterator_start
    (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    jump_raw_data_item_eta
    pm ml l
    (cbor_raw_match_fuel_share_t (Ghost.reveal n))
    (cbor_raw_match_fuel_gather_t (Ghost.reveal n));
  it
}
```

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_start_map_entry_raw_data_item_fuel
  (n: Ghost.erased nat)
  (pm: perm)
  (ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.mixed_list_match
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm ml l
returns it: IT.iterator (cbor_map_entry cbor_raw)
ensures
  (exists* pm'.
    I.iterator_match
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' it l **
    Trade.trade
      (I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm' it l)
      (I.mixed_list_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm ml l))
{
  let it = I.iterator_start
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    jump_nondep_then_raw_data_item_eta
    pm ml l
    (cbor_map_entry_vmatch_fuel_share_t (Ghost.reveal n))
    (cbor_map_entry_vmatch_fuel_gather_t (Ghost.reveal n));
  it
}
```

#pop-options

(* ====================================================================
   Non-inline by-value wrappers around iterator_next_eos for the two
   fuel-vmatch + parser combinations used by Det.Compare's array and
   map cases. iterator_next_eos is the canonical-comparison advancer
   (it yields elt_or_serialized so the comparator can byte-compare
   already-serialized data items without re-parsing them). Wrapping it
   non-inline pulls all of its working set (the base_mixed_list_next_n_eos
   loop, the iterator_start for the tail, the share/gather operations)
   out of the recursive comparator's stack frame.

   The wrappers take the iterator by value and return both the
   elt_or_serialized result and the advanced iterator by value, just
   like the iterator_next_*_fuel byval wrappers above.
==================================================================== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_eos_raw_data_item_fuel
  (n: Ghost.erased nat)
  (pm: perm)
  (x: IT.iterator cbor_raw)
  (l: Ghost.erased (list raw_data_item))
requires
  I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm
    x (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: (I.elt_or_serialized cbor_raw & IT.iterator cbor_raw)
ensures
  (exists* pm_v hd_val tl_l pm' .
    I.elt_or_serialized_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm_v (fst res) hd_val **
    I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm'
      (snd res) tl_l **
    Trade.trade
      (I.elt_or_serialized_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm_v (fst res) hd_val **
       I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm'
         (snd res) tl_l)
      (I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm
         x (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let mut r = x;
  let elt = I.iterator_next_eos
    (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    jump_raw_data_item_eta
    pm r _ l
    (cbor_raw_match_fuel_share_t (Ghost.reveal n))
    (cbor_raw_match_fuel_gather_t (Ghost.reveal n));
  unfold (I.iterator_next_eos_post (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    pm r x (Ghost.reveal l) elt);
  let x' = !r;
  (elt, x')
}
```

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_eos_map_entry_raw_data_item_fuel
  (n: Ghost.erased nat)
  (pm: perm)
  (x: IT.iterator (cbor_map_entry cbor_raw))
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.iterator_match
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm x (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: (I.elt_or_serialized (cbor_map_entry cbor_raw) & IT.iterator (cbor_map_entry cbor_raw))
ensures
  (exists* pm_v hd_val tl_l pm' .
    I.elt_or_serialized_match
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_v (fst res) hd_val **
    I.iterator_match
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' (snd res) tl_l **
    Trade.trade
      (I.elt_or_serialized_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm_v (fst res) hd_val **
       I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm' (snd res) tl_l)
      (I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm x (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let mut r = x;
  let elt = I.iterator_next_eos
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    jump_nondep_then_raw_data_item_eta
    pm r _ l
    (cbor_map_entry_vmatch_fuel_share_t (Ghost.reveal n))
    (cbor_map_entry_vmatch_fuel_gather_t (Ghost.reveal n));
  unfold (I.iterator_next_eos_post
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm r x (Ghost.reveal l) elt);
  let x' = !r;
  (elt, x')
}
```

#pop-options

(* ==================================================================
   By-ref iterator_next_eos wrappers.

   These mirror the byval wrappers above but take the iterator ref
   directly from the caller and update it in-place, returning only
   the elt_or_serialized result. This lets the caller avoid binding
   intermediate it_cur / it_n_new locals and the tuple letpattern
   that KaRaMeL emits for the (elt_or_serialized, iterator) return
   value of the byval variant. Used by Det.Compare's recursive
   array/map case helpers to shrink their per-recursion stack frame.
   ================================================================== *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_eos_raw_data_item_fuel_byref
  (n: Ghost.erased nat)
  (pm: perm)
  (r: R.ref (IT.iterator cbor_raw))
  (x: Ghost.erased (IT.iterator cbor_raw))
  (l: Ghost.erased (list raw_data_item))
requires
  R.pts_to r (Ghost.reveal x) **
  I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm
    (Ghost.reveal x) (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: I.elt_or_serialized cbor_raw
ensures
  (exists* pm_v hd_val tl_l pm' x' .
    R.pts_to r x' **
    I.elt_or_serialized_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm_v res hd_val **
    I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm' x' tl_l **
    Trade.trade
      (I.elt_or_serialized_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm_v res hd_val **
       I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm' x' tl_l)
      (I.iterator_match (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item pm
         (Ghost.reveal x) (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let elt = I.iterator_next_eos
    (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    jump_raw_data_item_eta
    pm r _ l
    (cbor_raw_match_fuel_share_t (Ghost.reveal n))
    (cbor_raw_match_fuel_gather_t (Ghost.reveal n));
  unfold (I.iterator_next_eos_post (cbor_raw_match_fuel (Ghost.reveal n)) parse_raw_data_item
    pm r (Ghost.reveal x) (Ghost.reveal l) elt);
  elt
}
```

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_eos_map_entry_raw_data_item_fuel_byref
  (n: Ghost.erased nat)
  (pm: perm)
  (r: R.ref (IT.iterator (cbor_map_entry cbor_raw)))
  (x: Ghost.erased (IT.iterator (cbor_map_entry cbor_raw)))
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  R.pts_to r (Ghost.reveal x) **
  I.iterator_match
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm (Ghost.reveal x) (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: I.elt_or_serialized (cbor_map_entry cbor_raw)
ensures
  (exists* pm_v hd_val tl_l pm' x' .
    R.pts_to r x' **
    I.elt_or_serialized_match
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_v res hd_val **
    I.iterator_match
      (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' x' tl_l **
    Trade.trade
      (I.elt_or_serialized_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm_v res hd_val **
       I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm' x' tl_l)
      (I.iterator_match
         (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm (Ghost.reveal x) (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let elt = I.iterator_next_eos
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    jump_nondep_then_raw_data_item_eta
    pm r _ l
    (cbor_map_entry_vmatch_fuel_share_t (Ghost.reveal n))
    (cbor_map_entry_vmatch_fuel_gather_t (Ghost.reveal n));
  unfold (I.iterator_next_eos_post
    (cbor_map_entry_vmatch_fuel (Ghost.reveal n))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm r (Ghost.reveal x) (Ghost.reveal l) elt);
  elt
}
```

#pop-options
