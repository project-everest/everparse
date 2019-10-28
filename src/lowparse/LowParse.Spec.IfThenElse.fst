module LowParse.Spec.IfThenElse
include LowParse.Spec.Combinators

module Seq = FStar.Seq

noextract
inline_for_extraction
noeq
type parse_ifthenelse_param = {
  parse_ifthenelse_tag_kind: parser_kind;
  parse_ifthenelse_tag_t: Type;
  parse_ifthenelse_tag_parser: parser parse_ifthenelse_tag_kind parse_ifthenelse_tag_t;
  parse_ifthenelse_tag_cond: (parse_ifthenelse_tag_t -> Tot bool);
  parse_ifthenelse_payload_t: (bool -> Tot Type);
  parse_ifthenelse_payload_parser: ((b: bool) -> Tot (k: parser_kind & parser k (parse_ifthenelse_payload_t b)));
  parse_ifthenelse_t: Type;
  parse_ifthenelse_synth: ((t: parse_ifthenelse_tag_t) -> (parse_ifthenelse_payload_t (parse_ifthenelse_tag_cond t)) -> GTot parse_ifthenelse_t);
  parse_ifthenelse_synth_injective: (
    (t1: parse_ifthenelse_tag_t) ->
    (x1: parse_ifthenelse_payload_t (parse_ifthenelse_tag_cond t1)) ->
    (t2: parse_ifthenelse_tag_t) ->
    (x2: parse_ifthenelse_payload_t (parse_ifthenelse_tag_cond t2)) ->
    Lemma
    (requires (parse_ifthenelse_synth t1 x1 == parse_ifthenelse_synth t2 x2))
              (ensures (t1 == t2 /\ coerce (parse_ifthenelse_payload_t (parse_ifthenelse_tag_cond t2)) x1 == x2))
  );
}

inline_for_extraction
let parse_ifthenelse_payload_kind
  (p: parse_ifthenelse_param)
: Tot parser_kind
= glb (dfst (p.parse_ifthenelse_payload_parser true)) (dfst (p.parse_ifthenelse_payload_parser false))

inline_for_extraction
let parse_ifthenelse_kind
  (p: parse_ifthenelse_param)
: Tot parser_kind
= and_then_kind p.parse_ifthenelse_tag_kind (parse_ifthenelse_payload_kind p)

let parse_ifthenelse_synth_injective (p: parse_ifthenelse_param) (t: p.parse_ifthenelse_tag_t) : Lemma (synth_injective (p.parse_ifthenelse_synth t)) [SMTPat (synth_injective (p.parse_ifthenelse_synth t))] =
  Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (p.parse_ifthenelse_synth_injective t x1 t) x2)

let parse_ifthenelse_payload (p: parse_ifthenelse_param) (t: p.parse_ifthenelse_tag_t) : Tot (parser (parse_ifthenelse_payload_kind p) p.parse_ifthenelse_t) =
  weaken (parse_ifthenelse_payload_kind p) (parse_synth (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond t))) (p.parse_ifthenelse_synth t))

let parse_ifthenelse_payload_and_then_cases_injective  (p: parse_ifthenelse_param) : Lemma
  (and_then_cases_injective (parse_ifthenelse_payload p))
  [SMTPat (and_then_cases_injective (parse_ifthenelse_payload p))]
= and_then_cases_injective_intro
    (parse_ifthenelse_payload p)
    (fun t1 t2 b1 b2 ->
      parse_synth_eq (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond t1))) (p.parse_ifthenelse_synth t1) b1;
      parse_synth_eq (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond t2))) (p.parse_ifthenelse_synth t2) b2;
      let Some (x1, _) = parse (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond t1))) b1 in
      let Some (x2, _) = parse (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond t2))) b2 in
      p.parse_ifthenelse_synth_injective t1 x1 t2 x2
    )

let parse_ifthenelse (p: parse_ifthenelse_param) : Tot (parser (parse_ifthenelse_kind p) p.parse_ifthenelse_t) =
  and_then p.parse_ifthenelse_tag_parser (parse_ifthenelse_payload p)

let parse_ifthenelse_eq
  (p: parse_ifthenelse_param)
  (input: bytes)
: Lemma
  (parse (parse_ifthenelse p) input == (
    match parse p.parse_ifthenelse_tag_parser input with
    | None -> None
    | Some (t, consumed_t) ->
      let b = p.parse_ifthenelse_tag_cond t in
      let input' = Seq.slice input consumed_t (Seq.length input) in
      match parse (dsnd (p.parse_ifthenelse_payload_parser b)) input' with
      | None -> None
      | Some (x, consumed_x) -> Some (p.parse_ifthenelse_synth t x, consumed_t + consumed_x)
  ))
= and_then_eq p.parse_ifthenelse_tag_parser (parse_ifthenelse_payload p) input;
  match parse p.parse_ifthenelse_tag_parser input with
  | None -> ()
  | Some (t, consumed_t) ->
      let b = p.parse_ifthenelse_tag_cond t in
      let input' = Seq.slice input consumed_t (Seq.length input) in
      let f : (p.parse_ifthenelse_payload_t (p.parse_ifthenelse_tag_cond t) -> GTot p.parse_ifthenelse_t) = (p.parse_ifthenelse_synth) t in
      let f' = coerce (p.parse_ifthenelse_payload_t b -> GTot p.parse_ifthenelse_t) f in
      parse_synth_eq
        #(dfst (p.parse_ifthenelse_payload_parser b))
        #(p.parse_ifthenelse_payload_t b)
        #(p.parse_ifthenelse_t)
        (dsnd (p.parse_ifthenelse_payload_parser b)) f' input'

noextract
inline_for_extraction
noeq
type serialize_ifthenelse_param (p: parse_ifthenelse_param) = {
  serialize_ifthenelse_tag_serializer: serializer p.parse_ifthenelse_tag_parser;
  serialize_ifthenelse_payload_serializer: ((b: bool) -> Tot (serializer (dsnd (p.parse_ifthenelse_payload_parser b))));
  serialize_ifthenelse_synth_recip: (p.parse_ifthenelse_t -> GTot ( t: p.parse_ifthenelse_tag_t & (p.parse_ifthenelse_payload_t (p.parse_ifthenelse_tag_cond t))));
  serialize_ifthenelse_synth_inverse: (
    (x: p.parse_ifthenelse_t) ->
    Lemma
    (let (| t, y |) = serialize_ifthenelse_synth_recip x in
      p.parse_ifthenelse_synth t y == x)
  );
}

let bare_serialize_ifthenelse
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Tot (bare_serializer p.parse_ifthenelse_t)
= fun (d: p.parse_ifthenelse_t) ->
  let (| t, y |) = s.serialize_ifthenelse_synth_recip d in
  Seq.append (serialize s.serialize_ifthenelse_tag_serializer t) (serialize (s.serialize_ifthenelse_payload_serializer (p.parse_ifthenelse_tag_cond t)) y)

let bare_serialize_ifthenelse_correct
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
: Lemma
  (requires (p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong))
  (ensures (serializer_correct (parse_ifthenelse p) (bare_serialize_ifthenelse s)))
= let prf
    (x: p.parse_ifthenelse_t)
  : Lemma
    (let sq = bare_serialize_ifthenelse s x in
     parse (parse_ifthenelse p) sq == Some (x, Seq.length sq))
  = let sq = bare_serialize_ifthenelse s x in
    parse_ifthenelse_eq p sq;
    let (| t, y |) = s.serialize_ifthenelse_synth_recip x in
    let sqt = serialize s.serialize_ifthenelse_tag_serializer t in
    let sqp = serialize (s.serialize_ifthenelse_payload_serializer (p.parse_ifthenelse_tag_cond t)) y in
    parse_strong_prefix p.parse_ifthenelse_tag_parser sqt sq;
    assert (Seq.slice sq (Seq.length sqt) (Seq.length sq) `Seq.equal` sqp);
    s.serialize_ifthenelse_synth_inverse x
  in
  Classical.forall_intro prf

let serialize_ifthenelse
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p { p.parse_ifthenelse_tag_kind.parser_kind_subkind == Some ParserStrong } )
: Tot (serializer (parse_ifthenelse p))
= bare_serialize_ifthenelse_correct s;
  bare_serialize_ifthenelse s

let serialize_ifthenelse_synth_inverse'
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (tg: p.parse_ifthenelse_tag_t)
  (pl: p.parse_ifthenelse_payload_t (p.parse_ifthenelse_tag_cond tg))
: Lemma
  (s.serialize_ifthenelse_synth_recip (p.parse_ifthenelse_synth tg pl) == (| tg, pl |))
= let (| tg', pl' |) = s.serialize_ifthenelse_synth_recip (p.parse_ifthenelse_synth tg pl) in
  s.serialize_ifthenelse_synth_inverse (p.parse_ifthenelse_synth tg pl);
  p.parse_ifthenelse_synth_injective tg pl tg' pl'

let parse_ifthenelse_parse_tag_payload
  (#p: parse_ifthenelse_param)
  (s: serialize_ifthenelse_param p)
  (input: bytes)
: Lemma
  (requires (Some? (parse (parse_ifthenelse p) input)))
  (ensures (
    let Some (x, _) = parse (parse_ifthenelse p) input in
    match parse p.parse_ifthenelse_tag_parser input with
    | None -> False
    | Some (tg, consumed) ->
      let input' = Seq.slice input consumed (Seq.length input) in
      begin match parse (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond tg))) input' with
      | None -> False
      | Some (pl, consumed') ->
        s.serialize_ifthenelse_synth_recip x == (| tg, pl |)
      end
  ))
= parse_ifthenelse_eq p input;
  let Some (t, consumed) = parse p.parse_ifthenelse_tag_parser input in
  let input' = Seq.slice input consumed (Seq.length input) in
  let Some (t1, _) = parse (dsnd (p.parse_ifthenelse_payload_parser (p.parse_ifthenelse_tag_cond t))) input' in
  serialize_ifthenelse_synth_inverse' s t t1
