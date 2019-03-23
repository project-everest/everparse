module LowParse.SLow.IfThenElse
include LowParse.Spec.IfThenElse
include LowParse.SLow.Combinators

module B32 = LowParse.Bytes32
module U32 = FStar.UInt32

inline_for_extraction
let parse32_ifthenelse
  (p: parse_ifthenelse_param)
  (pt32: parser32 p.parse_ifthenelse_tag_parser)
  (b32: (t: p.parse_ifthenelse_tag_t) -> Tot (b: bool { b == p.parse_ifthenelse_tag_cond t } ))
  (pp32: (b: bool) -> Tot (parser32 (dsnd (p.parse_ifthenelse_payload_parser b))))
  (synt: (b: bool) -> (t: p.parse_ifthenelse_tag_t { b == p.parse_ifthenelse_tag_cond t } ) -> (pl: p.parse_ifthenelse_payload_t b) -> Tot (y: p.parse_ifthenelse_t { y == p.parse_ifthenelse_synth t pl } ))
: Tot (parser32 (parse_ifthenelse p))
= fun input ->
  ((
    [@inline_let]
    let _ = parse_ifthenelse_eq p (B32.reveal input) in
    match pt32 input with
    | None -> None
    | Some (t, consumed_t) ->
      let b = b32 t in
      let input' = B32.slice input consumed_t (B32.len input) in
      if b
      then
        match pp32 true input' with
        | None -> None
        | Some (pl, consumed_pl) ->
          Some (synt true t pl, consumed_t `U32.add` consumed_pl)
      else
        match pp32 false input' with
        | None -> None
        | Some (pl, consumed_pl) ->
          Some (synt false t pl, consumed_t `U32.add` consumed_pl)
  ) <: (res: _ { parser32_correct (parse_ifthenelse p) input res } )
  )

inline_for_extraction
let serialize32_ifthenelse
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p {
    let tk = p.parse_ifthenelse_tag_kind in
    tk.parser_kind_subkind == Some ParserStrong /\
    Some? tk.parser_kind_high /\
    Some? (dfst (p.parse_ifthenelse_payload_parser true)).parser_kind_high /\
    Some? (dfst (p.parse_ifthenelse_payload_parser false)).parser_kind_high /\
    Some?.v tk.parser_kind_high + Some?.v (dfst (p.parse_ifthenelse_payload_parser true)).parser_kind_high < 4294967296 /\
    Some?.v tk.parser_kind_high + Some?.v (dfst (p.parse_ifthenelse_payload_parser false)).parser_kind_high < 4294967296
  })
  (st32: serializer32 s.serialize_ifthenelse_tag_serializer)
  (syntt: (x: p.parse_ifthenelse_t) -> Tot (t: p.parse_ifthenelse_tag_t { t == dfst (s.serialize_ifthenelse_synth_recip x) } ))
  (b32: (t: p.parse_ifthenelse_tag_t) -> Tot (b: bool { b == p.parse_ifthenelse_tag_cond t } ))
  (syntp: (b: bool) -> (x: p.parse_ifthenelse_t { b == p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) } ) -> Tot (pl: p.parse_ifthenelse_payload_t b { pl == dsnd (s.serialize_ifthenelse_synth_recip x) } ))
  (sp32: (b: bool) -> Tot (serializer32 (s.serialize_ifthenelse_payload_serializer b)))
: Tot (serializer32 (serialize_ifthenelse s))
= fun (input: p.parse_ifthenelse_t) -> ((
    let t = syntt input in
    let st = st32 t in
    let b = b32 t in
    if b
    then
      let y = syntp true input in
      B32.append st (sp32 true y)
    else
      let y = syntp false input in
      B32.append st (sp32 false y)
  ) <: (res: _ { serializer32_correct (serialize_ifthenelse s) input res }))

inline_for_extraction
let size32_ifthenelse
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p {
    let tk = p.parse_ifthenelse_tag_kind in
    tk.parser_kind_subkind == Some ParserStrong /\
    Some? tk.parser_kind_high /\
    Some? (dfst (p.parse_ifthenelse_payload_parser true)).parser_kind_high /\
    Some? (dfst (p.parse_ifthenelse_payload_parser false)).parser_kind_high /\
    Some?.v tk.parser_kind_high + Some?.v (dfst (p.parse_ifthenelse_payload_parser true)).parser_kind_high < 4294967296 /\
    Some?.v tk.parser_kind_high + Some?.v (dfst (p.parse_ifthenelse_payload_parser false)).parser_kind_high < 4294967296
  })
  (st32: size32 s.serialize_ifthenelse_tag_serializer)
  (syntt: (x: p.parse_ifthenelse_t) -> Tot (t: p.parse_ifthenelse_tag_t { t == dfst (s.serialize_ifthenelse_synth_recip x) } ))
  (b32: (t: p.parse_ifthenelse_tag_t) -> Tot (b: bool { b == p.parse_ifthenelse_tag_cond t } ))
  (syntp: (b: bool) -> (x: p.parse_ifthenelse_t { b == p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) } ) -> Tot (pl: p.parse_ifthenelse_payload_t b { pl == dsnd (s.serialize_ifthenelse_synth_recip x) } ))
  (sp32: (b: bool) -> Tot (size32 (s.serialize_ifthenelse_payload_serializer b)))
: Tot (size32 (serialize_ifthenelse s))
= fun (input: p.parse_ifthenelse_t) -> ((
    let t = syntt input in
    let st = st32 t in
    let b = b32 t in
    if b
    then
      let y = syntp true input in
      U32.add st (sp32 true y)
    else
      let y = syntp false input in
      U32.add st (sp32 false y)
  ) <: (res: _ { size32_postcond (serialize_ifthenelse s) input res }))
