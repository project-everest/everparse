module LowParse.Pulse.BitSum
include LowParse.Spec.BitSum
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Stick
open Pulse.Lib.Slice

#push-options "--print_universes"

inline_for_extraction
```pulse
fn stt_cps_ifthenelse
  (#t: Type0)
  (y: Ghost.erased t)
: if_combinator_weak u#4 (stt_cps u#0 #t y)
= (cond: _)
  (ftrue: _)
  (ffalse: _)
  (pre: _)
  (t': Type0)
  (post: _)
  (y': _)
{
  if cond {
    ftrue () pre t' post y'
  } else {
    ffalse () pre t' post y'
  }
}
```

inline_for_extraction
let validate_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (f: filter_bitsum'_t b)
  (d: destr_bitsum'_t b)
  (#k: parser_kind)
  (#p: parser k t)
  (w: validate_and_read p)
: Pure (validate_and_read (tot_parse_bitsum' b p))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
    (validate_and_read_synth
      (validate_and_read_filter
        w
        (filter_bitsum' b)
        (fun x -> f x)
      )
      (synth_bitsum' b)
      (d
        stt_cps
        stt_cps_ifthenelse
        (fun k pre t' post phi -> phi k)
      )
    )

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
```pulse
fn read_bitsum'_cont
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (k_: bitsum'_type b)
  (pre: vprop)
  (t': Type0)
  (post: (t' -> vprop))
  (phi: (k': bitsum'_type b { k' == k_ }) -> stt t' pre (fun x -> post x))
  requires pre
  returns x: t'
  ensures post x
{
  phi k_
}
```

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
        stt_cps
        stt_cps_ifthenelse
        (read_bitsum'_cont b)
    )
