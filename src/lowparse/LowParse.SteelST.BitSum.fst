module LowParse.SteelST.BitSum
include LowParse.Spec.BitSum
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
include LowParse.SteelST.Combinators

inline_for_extraction
let validate_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (f: filter_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (w: validator p)
  (r: cps_reader p)
: Pure (validator (parse_bitsum' b p))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  rewrite_validator
    (validate_synth
      (validate_filter_with_cps_reader
        w
        r
        (filter_bitsum' b)
        (fun x -> f x)
      )
      (synth_bitsum' b)
      ()
    )
    _

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
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  jump_synth
    (jump_filter
      w
      (filter_bitsum' b)
    )
    (synth_bitsum' b)
    ()

inline_for_extraction
let read_bitsum'
  (#t: eqtype)
  (#tot: pos)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (d: destr_bitsum'_t b)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: cps_reader p)
: Tot (cps_reader (parse_bitsum' b p))
= [@@inline_let]
  let _ = synth_bitsum'_injective b in
  cps_read_synth
    (cps_read_filter
      r
      (filter_bitsum' b)
    )
    (synth_bitsum' b)
    (
      d
        cps_read_synth_cont
        (fun k cond iftrue iffalse pre t' post phi ->
          if cond
          then iftrue () pre t' post phi
          else iffalse () pre t' post phi
        )
        (fun k pre t' post phi -> phi k)
    )
    ()
