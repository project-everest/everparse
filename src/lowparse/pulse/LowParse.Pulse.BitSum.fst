module LowParse.Pulse.BitSum
include LowParse.Spec.BitSum
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Slice

#push-options "--print_universes"

inline_for_extraction
let jump_bitsum' 
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: parser_kind)
  (#p: parser k t)
  (w: jumper p)
: Tot (jumper (tot_parse_bitsum' b p))
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
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: reader s)
: Tot (reader (tot_serialize_bitsum' b s))
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
