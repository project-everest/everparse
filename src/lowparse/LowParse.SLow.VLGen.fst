module LowParse.SLow.VLGen
include LowParse.SLow.Combinators
include LowParse.SLow.FLData
include LowParse.Spec.VLGen

module U32 = FStar.UInt32
module B32 = LowParse.Bytes32

inline_for_extraction
let parse32_bounded_vlgen
  (vmin: der_length_t)
  (min: U32.t { U32.v min == vmin } )
  (vmax: der_length_t)
  (max: U32.t { U32.v max == vmax /\ U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (U32.v min) (U32.v max)))
  (pk32: parser32 pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
: Tot (parser32 (parse_bounded_vlgen (vmin) (vmax) pk s))
= fun (input: bytes32) -> ((
    [@inline_let]
    let _ = parse_bounded_vlgen_unfold_aux (U32.v min) (U32.v max) pk s (B32.reveal input) in
    match pk32 input with
    | None -> None
    | Some (sz, consumed) ->
      let input' = B32.slice input consumed (B32.len input) in
      match parse32_fldata_strong s p32 (U32.v sz) sz input' with
      | None -> None
      | Some (x, consumed') -> Some ((x <: parse_bounded_vldata_strong_t (U32.v min) (U32.v max) s), consumed `U32.add` consumed')
  ) <: (res: _ { parser32_correct (parse_bounded_vlgen (U32.v min) (U32.v max) pk s) input res } ))

inline_for_extraction
let parse32_vlgen
  (vmin: nat)
  (min: U32.t { U32.v min == vmin } )
  (vmax: nat)
  (max: U32.t { U32.v max == vmax /\ U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (U32.v min) (U32.v max)))
  (pk32: parser32 pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (U32.v min) (U32.v max) k } )
  (p32: parser32 p)
: Tot (parser32 (parse_vlgen (vmin) (vmax) pk s))
= parse32_synth'
    _
    (synth_vlgen (U32.v min) (U32.v max) s)
    (parse32_bounded_vlgen vmin min vmax max pk32 s p32)
    ()

let serialize32_bounded_vlgen_precond
  (min: nat)
  (max: nat { min <= max } )
  (sk: parser_kind)
  (k: parser_kind)
: GTot bool
= match sk.parser_kind_high with
  | None -> false
  | Some kmax -> 
    let max' = match k.parser_kind_high with
    | None -> max
    | Some km -> if km < max then km else max
    in
    kmax + max' < 4294967296

inline_for_extraction
let serialize32_bounded_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 min max))
  (#ssk: serializer pk)
  (ssk32: serializer32 ssk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s { serialize32_bounded_vlgen_precond min max sk k } )
: Tot (serializer32 (serialize_bounded_vlgen min max ssk s))
= fun (input: parse_bounded_vldata_strong_t min max s) -> ((
    [@inline_let]
    let _ = serialize_bounded_vlgen_unfold min max ssk s input in
    let sp = s32 input in
    let len = B32.len sp in
    ssk32 len `B32.append` sp
  ) <: (res: _ { serializer32_correct (serialize_bounded_vlgen min max ssk s) input res } ))

inline_for_extraction
let serialize32_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 min max))
  (#ssk: serializer pk)
  (ssk32: serializer32 ssk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s { parse_vlgen_precond min max k /\ serialize32_bounded_vlgen_precond min max sk k } )
: Tot (serializer32 (serialize_vlgen min max ssk s))
= serialize32_synth'
    _
    (synth_vlgen min max s)
    _
    (serialize32_bounded_vlgen min max ssk32 s32)
    (synth_vlgen_recip min max s)
    ()

inline_for_extraction
let size32_bounded_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 min max))
  (#ssk: serializer pk)
  (ssk32: size32 ssk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s {  serialize32_bounded_vlgen_precond min max sk k } )
: Tot (size32 (serialize_bounded_vlgen min max ssk s))
= fun (input: parse_bounded_vldata_strong_t min max s) -> ((
    [@inline_let]
    let _ = serialize_bounded_vlgen_unfold min max ssk s input in
    let sp = s32 input in
    ssk32 sp `U32.add` sp
  ) <: (res: _ { size32_postcond (serialize_bounded_vlgen min max ssk s) input res } ))

inline_for_extraction
let size32_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 min max))
  (#ssk: serializer pk)
  (ssk32: size32 ssk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s { parse_vlgen_precond min max k /\ serialize32_bounded_vlgen_precond min max sk k } )
: Tot (size32 (serialize_vlgen min max ssk s))
= size32_synth'
    _
    (synth_vlgen min max s)
    _
    (size32_bounded_vlgen min max ssk32 s32)
    (synth_vlgen_recip min max s)
    ()
