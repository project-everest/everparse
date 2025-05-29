module LowParse.Pulse.BitSum
#lang-pulse
include LowParse.Spec.BitSum
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice

#push-options "--print_universes"

inline_for_extraction
let jump_bitsum' 
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: jumper p)
: Tot (jumper (parse_bitsum' b p))
= jump_synth
    (jump_filter
      w
      (filter_bitsum' b)
    )
    (synth_bitsum'_injective b; synth_bitsum' b)

inline_for_extraction
let read_synth_cont_ifthenelse
  (#t: Type0)
  (x: Ghost.erased t)
: Tot (if_combinator_weak (read_synth_cont_t #t x))
= fun cond iftrue iffalse t' g' -> if cond then iftrue () t' g' else iffalse () t' g'

inline_for_extraction
let read_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (d: destr_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: reader s)
: Tot (reader (serialize_bitsum' b s))
= read_synth
    (read_filter
      r
      (filter_bitsum' b)
    )
    (synth_bitsum'_injective b; synth_bitsum' b)
    (synth_bitsum'_recip_inverse b; synth_bitsum'_recip b)
    (
      d
        (read_synth_cont_t #(bitsum'_type b))
        (read_synth_cont_ifthenelse #(bitsum'_type b))
        (read_synth_cont_init)
    )

inline_for_extraction
fn l2r_write_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (sr: synth_bitsum'_recip_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_leaf_writer s)
: (l2r_leaf_writer u#0 #(bitsum'_type b) #(parse_filter_kind k) #(parse_bitsum' b p) (serialize_bitsum' b s))
= (x: _)
  (out: _)
  (offset: _)
  (#v: Ghost.erased bytes)
{
  serialize_bitsum'_eq b s x;
  synth_bitsum'_injective b;
  synth_bitsum'_recip_inverse b;
  w (sr x) out offset
}

inline_for_extraction
fn compute_remaining_size_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (sr: synth_bitsum'_recip_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_compute_remaining_size s)
: (leaf_compute_remaining_size #(bitsum'_type b) #(parse_filter_kind k) #(parse_bitsum' b p) (serialize_bitsum' b s))
= (x: _)
  (out: _)
  (#v: Ghost.erased bytes)
{
  serialize_bitsum'_eq b s x;
  synth_bitsum'_injective b;
  synth_bitsum'_recip_inverse b;
  w (sr x) out
}
