module LowParse.Spec.Base
include LowParse.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

let parser_kind_prop = parser_kind_prop'

let parser_kind_prop_equiv
  (#t: Type) (k: parser_kind) (f: bare_parser t)
: Lemma
  (parser_kind_prop k f <==> parser_kind_prop' k f)
= ()

let parser_kind_prop_ext
  (#t: Type)
  (k: parser_kind)
  (f1 f2: bare_parser t)
: Lemma
  (requires (forall (input: bytes) . parse f1 input == parse f2 input))
  (ensures (parser_kind_prop k f1 <==> parser_kind_prop k f2))
= no_lookahead_ext f1 f2;
  injective_ext f1 f2

let is_weaker_than_correct
  (k1: parser_kind)
  (k2: parser_kind)
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (requires (parser_kind_prop k2 f /\ k1 `is_weaker_than` k2))
  (ensures (parser_kind_prop k1 f))
= ()

let parse_injective
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
: Lemma
  (requires (
    injective_precond p input1 input2
  ))
  (ensures (
    injective_postcond p input1 input2
  ))
= ()

let parse_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\ (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      Seq.slice input1 0 consumed `Seq.equal` Seq.slice input2 0 consumed
    | _ -> False
  )))
  (ensures (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      parse p input2 == Some (x, consumed)
    | _ -> False
  ))
= assert (no_lookahead_on p input1 input2);
  assert (injective_postcond p input1 input2)

let serializer_correct_implies_complete
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: bare_serializer t)
: Lemma
  (requires (serializer_correct p f))
  (ensures (serializer_complete p f))
= let prf
    (s: bytes)
  : Lemma
    (requires (Some? (parse p s)))
    (ensures (
      Some? (parse p s) /\ (
      let (Some (x, len)) = parse p s in
      f x == Seq.slice s 0 len
    )))
  = let (Some (x, len)) = parse p s in
    assert (injective_precond p (f x) s);
    assert (injective_postcond p (f x) s)
  in
  Classical.forall_intro (Classical.move_requires prf)

let serializer_parser_unique'
  (#k1: parser_kind)
  (#t: Type)
  (p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    is_strong p1 /\
    is_strong p2 /\
    serializer_correct p1 s /\
    serializer_correct p2 s /\
    Some? (parse p1 x)
  ))
  (ensures (
    parse p1 x == parse p2 x
  ))
= serializer_correct_implies_complete p1 s;
  let (Some (y, len)) = parse p1 x in
  let x' = Seq.slice x 0 len in
  assert (s y == x');
  let len' = Seq.length x' in
  assert (len == len');
  assert (parse p1 x' == Some (y, len'));
  assert (parse p2 x' == Some (y, len'));
  assert (no_lookahead_on p2 x' x);
  assert (no_lookahead_on_postcond p2 x' x);
  assert (injective_postcond p2 x' x)

let serialize_length
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (let x = Seq.length (serialize s x) in
   k.parser_kind_low <= x /\ (
   match k.parser_kind_high with
   | None -> True
   | Some y -> x <= y
  ))
  [SMTPat (Seq.length (serialize s x))]
= assert (Some? (parse p (serialize s x)))

let serialize_not_fail
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (k.parser_kind_metadata <> Some ParserKindMetadataFail)
  [SMTPat (serialize s x)]
= assert (Some? (parse p (serialize s x)))
