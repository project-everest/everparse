module CBOR.Pulse.Raw.EverParse.ReadMapEntry
#lang-pulse

include CBOR.Pulse.Raw.EverParse.Type
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Read
open LowParse.Spec.Combinators
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Combinators
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module Validate = CBOR.Pulse.Raw.EverParse.Validate
module RawMake = CBOR.Pulse.Raw.EverParse.Make
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module R = Pulse.Lib.Reference

(* ====================================================================
   cbor_raw_read_map_entry: zero-copy parser for serialized map entries
   ((nondep_then parse_raw_data_item parse_raw_data_item)) into a
   cbor_map_entry cbor_raw value with the cbor_map_entry_match relation.

   Used by the map iterator's iterator_next, where the underlying
   mixed_list has serialized regions that must be parsed on the fly
   into pairs of cbor_raw values. ==================================================== *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

```pulse
fn cbor_raw_read_map_entry
  (pm: perm)
  (f64: squash SZ.fits_u64)
: PPB.zero_copy_parse_strong_prefix #(cbor_map_entry cbor_raw) #(raw_data_item & raw_data_item)
    (cbor_map_entry_match cbor_raw_match pm)
    #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)
    (nondep_then parse_raw_data_item parse_raw_data_item)
= (input: S.slice byte)
  (#pms: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
{
  let split_input = split_nondep_then_strong_prefix
    #raw_data_item #raw_data_item
    #parse_raw_data_item_kind #parse_raw_data_item
    #parse_raw_data_item_kind #parse_raw_data_item
    (Validate.jump_raw_data_item f64)
    input
    ();
  match split_input { Mktuple2 input1 input2 -> {
  unfold (split_nondep_then_strong_prefix_post
    parse_raw_data_item parse_raw_data_item input pms v (input1, input2));
  let xk = cbor_raw_read pm f64 input1 #(pms /. 2.0R) #(Ghost.hide (fst (Ghost.reveal v)));
  Trade.trans_hyp_l
    (cbor_raw_match pm xk (fst (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix parse_raw_data_item input1 #(pms /. 2.0R) (fst (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix parse_raw_data_item input2 #(pms /. 2.0R) (snd (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pms v);
  let xv = cbor_raw_read pm f64 input2 #(pms /. 2.0R) #(Ghost.hide (snd (Ghost.reveal v)));
  Trade.trans_hyp_r
    (cbor_raw_match pm xk (fst (Ghost.reveal v)))
    (cbor_raw_match pm xv (snd (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix parse_raw_data_item input2 #(pms /. 2.0R) (snd (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pms v);
  let res = RawMake.cbor_mk_map_entry xk xv
    #pm #(Ghost.hide (fst (Ghost.reveal v))) #(Ghost.hide (snd (Ghost.reveal v)));
  Trade.trans
    (cbor_map_entry_match cbor_raw_match pm res (fst (Ghost.reveal v), snd (Ghost.reveal v)))
    (cbor_raw_match pm xk (fst (Ghost.reveal v)) ** cbor_raw_match pm xv (snd (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pms v);
  rewrite (cbor_map_entry_match cbor_raw_match pm res (fst (Ghost.reveal v), snd (Ghost.reveal v)))
       as (cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal v));
  rewrite (Trade.trade
    (cbor_map_entry_match cbor_raw_match pm res (fst (Ghost.reveal v), snd (Ghost.reveal v)))
    (PPB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pms v))
       as (Trade.trade
    (cbor_map_entry_match cbor_raw_match pm res (Ghost.reveal v))
    (PPB.pts_to_parsed_strong_prefix (nondep_then parse_raw_data_item parse_raw_data_item) input #pms v));
  res
  }}
}
```

#pop-options

(* ====================================================================
   Non-inline specializations of iterator_next for the two vmatch +
   parser combinations used by Det.Impl and Nondet.Common when
   advancing a CBOR array iterator (cbor_raw values) or map iterator
   (cbor_map_entry cbor_raw values). The bodies inline iterator_next
   once, baking in jumper and zero-copy parser. Callers therefore
   only need to provide pm, r, i_orig, l — no zcp / jumper passed
   at runtime, which keeps karamel from emitting partial-application
   warnings and keeps the call sites' stack frames small.
==================================================================== *)

ghost
fn cbor_raw_match_share_aux
  (x1: cbor_raw)
  (#pm0: perm)
  (#x2: raw_data_item)
requires cbor_raw_match pm0 x1 x2
ensures cbor_raw_match (pm0 /. 2.0R) x1 x2 ** cbor_raw_match (pm0 /. 2.0R) x1 x2
{
  cbor_raw_match_share x1 #pm0 #x2
}

ghost
fn cbor_raw_match_gather_aux
    (x1: cbor_raw)
    (#pm0: perm)
    (#x2: raw_data_item)
    (#pm0': perm)
    (#x2': raw_data_item)
requires cbor_raw_match pm0 x1 x2 ** cbor_raw_match pm0' x1 x2'
ensures cbor_raw_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
{
  cbor_raw_match_gather x1 #pm0 #x2 #pm0' #x2'
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* Take iterator by value and return a tuple (elt, new_iterator). This
   shape avoids over-constrained Rust lifetimes (where a `&'a mut [t<'a>]`
   would tie the mutable-borrow lifetime to the data lifetime), while
   still absorbing iterator_next's body into one non-inline wrapper so
   that callers do not inflate their stack frames. *)

```pulse
fn iterator_next_raw_data_item
  (f64: squash SZ.fits_u64)
  (pm: perm)
  (x: IT.iterator cbor_raw)
  (l: Ghost.erased (list raw_data_item))
requires
  I.iterator_match cbor_raw_match parse_raw_data_item pm x (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: (cbor_raw & IT.iterator cbor_raw)
ensures
  (exists* pm_v hd_val tl_l pm' .
    cbor_raw_match pm_v (fst res) hd_val **
    I.iterator_match cbor_raw_match parse_raw_data_item pm' (snd res) tl_l **
    Trade.trade
      (cbor_raw_match pm_v (fst res) hd_val **
       I.iterator_match cbor_raw_match parse_raw_data_item pm' (snd res) tl_l)
      (I.iterator_match cbor_raw_match parse_raw_data_item pm x (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let zcp = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read 1.0R f64) ();
  let mut r = x;
  let elt = I.iterator_next
    cbor_raw_match parse_raw_data_item
    Validate.jump_raw_data_item_eta
    pm r _ l
    cbor_raw_match_share_aux
    cbor_raw_match_gather_aux
    zcp;
  unfold (I.iterator_next_post cbor_raw_match parse_raw_data_item pm r x (Ghost.reveal l) elt);
  let x' = !r;
  (elt, x')
}
```

#pop-options

ghost
fn cbor_map_entry_match_share_aux
  (e: cbor_map_entry cbor_raw)
  (#pm0: perm)
  (#x2: (raw_data_item & raw_data_item))
requires cbor_map_entry_match cbor_raw_match pm0 e x2
ensures cbor_map_entry_match cbor_raw_match (pm0 /. 2.0R) e x2 **
        cbor_map_entry_match cbor_raw_match (pm0 /. 2.0R) e x2
{
  cbor_map_entry_match_share cbor_raw_match cbor_raw_match_share_aux e #pm0 #x2
}

ghost
fn cbor_map_entry_match_gather_aux
    (e: cbor_map_entry cbor_raw)
    (#pm0: perm)
    (#x2: (raw_data_item & raw_data_item))
    (#pm0': perm)
    (#x2': (raw_data_item & raw_data_item))
requires cbor_map_entry_match cbor_raw_match pm0 e x2 **
         cbor_map_entry_match cbor_raw_match pm0' e x2'
ensures cbor_map_entry_match cbor_raw_match (pm0 +. pm0') e x2 **
        pure (x2 == x2')
{
  ghost fn cbor_raw_match_gather_explicit
      (x1: cbor_raw)
      (#pm00: perm)
      (#xa: raw_data_item)
      (#pm00': perm)
      (xb: raw_data_item { xb << x2' })
    requires cbor_raw_match pm00 x1 xa ** cbor_raw_match pm00' x1 xb
    ensures cbor_raw_match (pm00 +. pm00') x1 xa ** pure (xa == xb)
  {
    cbor_raw_match_gather_aux x1 #pm00 #xa #pm00' #xb
  };
  cbor_map_entry_match_gather cbor_raw_match e #pm0 #x2 #pm0' #x2'
    cbor_raw_match_gather_explicit
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

```pulse
fn iterator_next_map_entry_raw_data_item
  (f64: squash SZ.fits_u64)
  (pm: perm)
  (x: IT.iterator (cbor_map_entry cbor_raw))
  (l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.iterator_match
    (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm x (Ghost.reveal l) **
  pure (Cons? (Ghost.reveal l))
returns res: (cbor_map_entry cbor_raw & IT.iterator (cbor_map_entry cbor_raw))
ensures
  (exists* pm_v hd_val tl_l pm' .
    cbor_map_entry_match cbor_raw_match pm_v (fst res) hd_val **
    I.iterator_match
      (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm' (snd res) tl_l **
    Trade.trade
      (cbor_map_entry_match cbor_raw_match pm_v (fst res) hd_val **
       I.iterator_match
         (cbor_map_entry_match cbor_raw_match)
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm' (snd res) tl_l)
      (I.iterator_match
         (cbor_map_entry_match cbor_raw_match)
         (nondep_then parse_raw_data_item parse_raw_data_item)
         pm x (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l))
{
  let zcp = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read_map_entry 1.0R f64) ();
  let mut r = x;
  let elt = I.iterator_next
    (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    Validate.jump_nondep_then_raw_data_item_eta
    pm r _ l
    cbor_map_entry_match_share_aux
    cbor_map_entry_match_gather_aux
    zcp;
  unfold (I.iterator_next_post
    (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm r x (Ghost.reveal l) elt);
  let x' = !r;
  (elt, x')
}
```

#pop-options
