module LowParse.PulseParse.BitSum
#lang-pulse
include LowParse.Spec.BitSum
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators

module LPB = LowParse.Pulse.BitSum

inline_for_extraction
let read_synth_cont_ifthenelse
  (#t: Type0)
  (x: Ghost.erased t)
: Tot (if_combinator_weak (PPC.read_synth_cont_t #t x))
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
  (r: PPB.reader p)
: Tot (PPB.reader (parse_bitsum' b p))
= PPC.read_synth
    (PPC.read_filter
      r
      (filter_bitsum' b)
    )
    (synth_bitsum'_injective b; synth_bitsum' b)
    (synth_bitsum'_recip_inverse b; synth_bitsum'_recip b)
    (
      d
        (PPC.read_synth_cont_t #(bitsum'_type b))
        (read_synth_cont_ifthenelse #(bitsum'_type b))
        (PPC.read_synth_cont_init)
    )
