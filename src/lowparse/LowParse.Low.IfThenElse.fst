module LowParse.Low.IfThenElse
include LowParse.Spec.IfThenElse
include LowParse.Low.Combinators

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

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
    Classical.move_requires (valid_ifthenelse_intro p h input) (uint64_to_uint32 pos);
    Classical.move_requires (valid_ifthenelse_elim p h input) (uint64_to_uint32 pos)
  in
  let pos_after_t = vt input pos in
  if is_error pos_after_t
  then pos_after_t
  else
    let b = test input (uint64_to_uint32 pos) in
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

let clens_ifthenelse_tag
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Tot (clens p.parse_ifthenelse_t p.parse_ifthenelse_tag_t)
= {
    clens_cond = (fun _ -> True);
    clens_get = (fun (x: p.parse_ifthenelse_t) -> dfst (s.serialize_ifthenelse_synth_recip x));
  }

let gaccessor_ifthenelse_tag'
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Tot (gaccessor' (parse_ifthenelse p) p.parse_ifthenelse_tag_parser (clens_ifthenelse_tag s))
= fun input ->
    parse_ifthenelse_eq p input;
    if Some? (parse (parse_ifthenelse p) input)
    then parse_ifthenelse_parse_tag_payload s input;
    0

let gaccessor_ifthenelse_tag
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Tot (gaccessor (parse_ifthenelse p) p.parse_ifthenelse_tag_parser (clens_ifthenelse_tag s))
= gaccessor_prop_equiv (parse_ifthenelse p) p.parse_ifthenelse_tag_parser (clens_ifthenelse_tag s) (gaccessor_ifthenelse_tag' s);
  gaccessor_ifthenelse_tag' s

inline_for_extraction
let accessor_ifthenelse_tag
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Tot (accessor (gaccessor_ifthenelse_tag s))
= fun #rrel #rel sl pos -> 
    let h = HST.get () in
    slice_access_eq h (gaccessor_ifthenelse_tag s) sl pos;
    pos

let clens_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
: Tot (clens p.parse_ifthenelse_t (p.parse_ifthenelse_payload_t b))
= {
    clens_cond = (fun (x: p.parse_ifthenelse_t) -> p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) == b);
    clens_get = (fun (x: p.parse_ifthenelse_t) -> dsnd (s.serialize_ifthenelse_synth_recip x) <: Ghost (p.parse_ifthenelse_payload_t b) (requires (p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) == b)) (ensures (fun _ -> True)));
  }

let gaccessor_ifthenelse_payload''
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
  (input: bytes)
: Ghost nat
  (requires (
    gaccessor_pre (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) input
  ))
  (ensures (fun res ->
    gaccessor_post' (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) input res
  ))
=   parse_ifthenelse_eq p input;
    parse_ifthenelse_parse_tag_payload s input;
    let Some (t, consumed) = parse p.parse_ifthenelse_tag_parser input in
    consumed

let gaccessor_ifthenelse_payload'
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
: Tot (gaccessor' (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b))
= fun (input: bytes) ->
    match parse (parse_ifthenelse p) input with
    | Some (x, _) ->
      if p.parse_ifthenelse_tag_cond (dfst (s.serialize_ifthenelse_synth_recip x)) = b
      then gaccessor_ifthenelse_payload'' s b input
      else 0 (* dummy *)
    | _ -> 0 (* dummy *)

let gaccessor_ifthenelse_payload_injective
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
  (sl sl' : bytes)
: Lemma
  (requires (
    gaccessor_pre (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) sl /\
    gaccessor_pre (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) sl' /\
    injective_precond (parse_ifthenelse p) sl sl'
  ))
  (ensures (gaccessor_ifthenelse_payload' s b sl == gaccessor_ifthenelse_payload' s b sl'))
= parse_ifthenelse_eq p sl;
  parse_ifthenelse_eq p sl';
  parse_ifthenelse_parse_tag_payload s sl;
  parse_ifthenelse_parse_tag_payload s sl' ;
  parse_injective p.parse_ifthenelse_tag_parser sl sl'

let gaccessor_ifthenelse_payload_no_lookahead
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
  (sl sl' : bytes)
: Lemma
  (requires (
    (parse_ifthenelse_kind p).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) sl /\
    gaccessor_pre (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) sl' /\
    no_lookahead_on_precond (parse_ifthenelse p) sl sl'
  ))
  (ensures (gaccessor_ifthenelse_payload' s b sl == gaccessor_ifthenelse_payload' s b sl'))
= parse_ifthenelse_eq p sl;
  parse_ifthenelse_eq p sl';
  parse_ifthenelse_parse_tag_payload s sl;
  parse_ifthenelse_parse_tag_payload s sl' ;
  parse_strong_prefix (parse_ifthenelse p) sl sl';
  parse_injective p.parse_ifthenelse_tag_parser sl sl'

let gaccessor_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (b: bool)
: Tot (gaccessor (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_ifthenelse_payload_injective s b x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_ifthenelse_payload_no_lookahead s b x));
  gaccessor_prop_equiv (parse_ifthenelse p) (dsnd (p.parse_ifthenelse_payload_parser b)) (clens_ifthenelse_payload s b) (gaccessor_ifthenelse_payload' s b);
  gaccessor_ifthenelse_payload' s b

inline_for_extraction
let accessor_ifthenelse_payload'
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (j: jumper p.parse_ifthenelse_tag_parser)
  (b: bool)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
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
    let large = bytes_of_slice_from h input pos in
    slice_access_eq h (gaccessor_ifthenelse_payload s b) input pos;
    valid_facts (parse_ifthenelse p) h input pos;
    parse_ifthenelse_eq p large;
    valid_facts p.parse_ifthenelse_tag_parser h input pos
  in
  j input pos

inline_for_extraction
let accessor_ifthenelse_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (j: jumper p.parse_ifthenelse_tag_parser)
  (b: bool)
: Tot (accessor (gaccessor_ifthenelse_payload s b))
= fun #rrel #rel -> accessor_ifthenelse_payload' s j b #rrel #rel
