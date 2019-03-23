module LowParse.Low.IfThenElse
include LowParse.Spec.IfThenElse
include LowParse.Low.Combinators

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let valid_ifthenelse_intro
  (p: parse_ifthenelse_param)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid p.parse_ifthenelse_tag_parser h sl pos /\ (
    let t = contents p.parse_ifthenelse_tag_parser h sl pos in
    let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
    let b = p.parse_ifthenelse_tag_cond t in
    valid (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t
  )))
  (ensures (
    valid p.parse_ifthenelse_tag_parser h sl pos /\ (
    let t = contents p.parse_ifthenelse_tag_parser h sl pos in
    let b = p.parse_ifthenelse_tag_cond t in
    let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
    valid (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t /\
    valid_content_pos
      (parse_ifthenelse p) h sl pos
      (p.parse_ifthenelse_synth
        t
        (contents (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
      )
      (get_valid_pos (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
  )))
= valid_facts (parse_ifthenelse p) h sl pos;
  valid_facts p.parse_ifthenelse_tag_parser h sl pos;
  let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
  let t = contents p.parse_ifthenelse_tag_parser h sl pos in
  let b = p.parse_ifthenelse_tag_cond t in
  valid_facts (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t;
  parse_ifthenelse_eq p (bytes_of_slice_from h sl pos)

let valid_ifthenelse_elim
  (p: parse_ifthenelse_param)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid (parse_ifthenelse p) h sl pos))
  (ensures (
    valid p.parse_ifthenelse_tag_parser h sl pos /\ (
    let t = contents p.parse_ifthenelse_tag_parser h sl pos in
    let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
    let b = p.parse_ifthenelse_tag_cond t in
    valid (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t /\
    valid_content_pos
      (parse_ifthenelse p) h sl pos
      (p.parse_ifthenelse_synth
        t
        (contents (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
      )
      (get_valid_pos (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t)
  )))
= valid_facts (parse_ifthenelse p) h sl pos;
  parse_ifthenelse_eq p (bytes_of_slice_from h sl pos);
  valid_facts p.parse_ifthenelse_tag_parser h sl pos;
  let pos_after_t = get_valid_pos p.parse_ifthenelse_tag_parser h sl pos in
  let t = contents p.parse_ifthenelse_tag_parser h sl pos in
  let b = p.parse_ifthenelse_tag_cond t in
  valid_facts (dsnd (p.parse_ifthenelse_payload_parser b)) h sl pos_after_t

inline_for_extraction
type test_ifthenelse_tag
  (p: parse_ifthenelse_param)
= (#rrel: _) -> (#rel: _) ->
  (input: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack bool
  (requires (fun h -> valid p.parse_ifthenelse_tag_parser h input pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == p.parse_ifthenelse_tag_cond (contents p.parse_ifthenelse_tag_parser h input pos)
  ))

inline_for_extraction
let validate_ifthenelse
  (p: parse_ifthenelse_param)
  (vt: validator p.parse_ifthenelse_tag_parser)
  (test: test_ifthenelse_tag p)
  (vp: (b: bool) -> Tot (validator (dsnd (p.parse_ifthenelse_payload_parser b))))
: Tot (validator (parse_ifthenelse p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.move_requires (valid_ifthenelse_intro p h input) pos;
    Classical.move_requires (valid_ifthenelse_elim p h input) pos
  in
  let pos_after_t = vt input pos in
  if validator_max_length `U32.lt` pos_after_t
  then pos_after_t
  else
    let b = test input pos in
    if b (* eta-expansion here *)
    then vp true input pos_after_t
    else vp false input pos_after_t

inline_for_extraction
let jump_ifthenelse
  (p: parse_ifthenelse_param)
  (vt: jumper p.parse_ifthenelse_tag_parser)
  (test: test_ifthenelse_tag p)
  (vp: (b: bool) -> Tot (jumper (dsnd (p.parse_ifthenelse_payload_parser b))))
: Tot (jumper (parse_ifthenelse p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.move_requires (valid_ifthenelse_elim p h input) pos
  in
  let pos_after_t = vt input pos in
  let b = test input pos in
  if b (* eta-expansion here *)
  then vp true input pos_after_t
  else vp false input pos_after_t

let clens_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
: Tot (clens p.parse_ifthenelse_t (p.parse_ifthenelse_payload_t b))
= {
    clens_cond = (fun (x: p.parse_ifthenelse_t) -> p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) == b);
    clens_get = (fun (x: p.parse_ifthenelse_t) -> dsnd (s.serialize_ifthenelse_synth_recip x) <: Ghost (p.parse_ifthenelse_payload_t b) (requires (p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) == b)) (ensures (fun _ -> True)));
  }

let gaccessor_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
: Tot (gaccessor (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b))
= fun (input: bytes) ->
    parse_ifthenelse_eq p input;
    let res =
      match parse p.parse_ifthenelse_tag_parser input with
      | Some (t, consumed) ->
        let b = p.parse_ifthenelse_tag_cond t in
        let input' = Seq.slice input consumed (Seq.length input) in
        begin match parse (dsnd (p.parse_ifthenelse_payload_parser b)) input' with
        | Some (x, _) ->
          s.serialize_ifthenelse_synth_inverse (p.parse_ifthenelse_synth t x);
          let (| t', x' |) = s.serialize_ifthenelse_synth_recip (p.parse_ifthenelse_synth t x) in
          p.parse_ifthenelse_synth_injective t x t' x';
          (consumed, Seq.length input - consumed)
        | _ -> (consumed, Seq.length input - consumed) (* must be the same value as in the Some case, for the stateful accessor, but no postcondition here in the ghost accessor *)
        end
      | _ -> (0, 0) (* dummy *)
    in
    (res <: (res: _ { gaccessor_post' (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) input res } ))

inline_for_extraction
let accessor_ifthenelse_payload'
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p { p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong  } )
  (j: jumper p.parse_ifthenelse_tag_parser)
  (b: bool)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    (get_parser_kind (parse_ifthenelse p)).parser_kind_subkind == Some ParserStrong /\
    (get_parser_kind (dsnd (p.parse_ifthenelse_payload_parser b))).parser_kind_subkind == Some ParserStrong /\
    valid (parse_ifthenelse p) h input pos /\
    (clens_ifthenelse_payload s b).clens_cond (contents (parse_ifthenelse p) h input pos)
  ))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h (gaccessor_ifthenelse_payload s b) input pos
  ))
= let h = HST.get () in
  [@inline_let]
  let _ =
    let pos' = get_valid_pos (parse_ifthenelse p) h input pos in
    let small = bytes_of_slice_from_to h input pos pos' in
    let large = bytes_of_slice_from h input pos in
    slice_access_eq h (gaccessor_ifthenelse_payload s b) input pos;
    valid_facts (parse_ifthenelse p) h input pos;
    parse_ifthenelse_eq p large;
    parse_ifthenelse_eq p small;
    parse_strong_prefix p.parse_ifthenelse_tag_parser large small;
    valid_facts p.parse_ifthenelse_tag_parser h input pos
  in
  j input pos

inline_for_extraction
let accessor_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p { p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong  } )
  (j: jumper p.parse_ifthenelse_tag_parser)
  (b: bool)
: Tot (accessor (gaccessor_ifthenelse_payload s b))
= fun #rrel #rel -> accessor_ifthenelse_payload' s j b #rrel #rel
