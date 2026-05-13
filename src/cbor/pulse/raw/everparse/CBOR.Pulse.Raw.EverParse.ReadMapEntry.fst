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
