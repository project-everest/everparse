module LowParse.Spec.Combinators
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

module T = FStar.Tactics

#reset-options "--using_facts_from '* -FStar.Tactis -FStar.Reflection'"

let and_then #k #t p #k' #t' p' =
  let f : bare_parser t' = and_then_bare p p' in
  and_then_correct p p' ;
  f

let and_then_eq
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
  (input: bytes)
: Lemma
  (requires (and_then_cases_injective p'))
  (ensures (parse (and_then p p') input == and_then_bare p p' input))
= ()

let parse_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
: Pure (parser k t2)
  (requires (
    synth_injective f2
  ))
  (ensures (fun _ -> True))
= coerce (parser k t2) (and_then p1 (fun v1 -> parse_fret f2 v1))

let parse_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (b: bytes)
: Lemma
  (requires (synth_injective f2))
  (ensures (parse (parse_synth p1 f2) b == parse_synth' p1 f2 b))
= ()

let bare_serialize_synth_correct #k #t1 #t2 p1 f2 s1 g1 =
  ()

let serialize_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer (parse_synth p1 f2))
= bare_serialize_synth_correct p1 f2 s1 g1;
  bare_serialize_synth p1 f2 s1 g1

let serialize_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x: t2)
: Lemma
  (serialize (serialize_synth p1 f2 s1 g1 u) x == serialize s1 (g1 x))
= ()

let serialize_synth_upd_chain
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x1: t1)
  (x2: t2)
  (y1: t1)
  (y2: t2)
  (i': nat)
  (s' : bytes)
: Lemma
  (requires (
    let s = serialize s1 x1 in
    i' + Seq.length s' <= Seq.length s /\
    serialize s1 y1 == seq_upd_seq s i' s' /\
    x2 == f2 x1 /\
    y2 == f2 y1
  ))
  (ensures (
    let s = serialize (serialize_synth p1 f2 s1 g1 u) x2 in
    i' + Seq.length s' <= Seq.length s /\
    Seq.length s == Seq.length (serialize s1 x1) /\
    serialize (serialize_synth p1 f2 s1 g1 u) y2 == seq_upd_seq s i' s'
  ))
= (* I don't know which are THE terms to exhibit among x1, x2, y1, y2 to make the patterns trigger *)
  assert (forall w w' . f2 w == f2 w' ==> w == w');
  assert (forall w . f2 (g1 w) == w)

let serialize_synth_upd_bw_chain
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x1: t1)
  (x2: t2)
  (y1: t1)
  (y2: t2)
  (i': nat)
  (s' : bytes)
: Lemma
  (requires (
    let s = serialize s1 x1 in
    i' + Seq.length s' <= Seq.length s /\
    serialize s1 y1 == seq_upd_bw_seq s i' s' /\
    x2 == f2 x1 /\
    y2 == f2 y1
  ))
  (ensures (
    let s = serialize (serialize_synth p1 f2 s1 g1 u) x2 in
    i' + Seq.length s' <= Seq.length s /\
    Seq.length s == Seq.length (serialize s1 x1) /\
    serialize (serialize_synth p1 f2 s1 g1 u) y2 == seq_upd_bw_seq s i' s'
  ))
= (* I don't know which are THE terms to exhibit among x1, x2, y1, y2 to make the patterns trigger *)
  assert (forall w w' . f2 w == f2 w' ==> w == w');
  assert (forall w . f2 (g1 w) == w)

let parse_tagged_union #kt #tag_t pt #data_t tag_of_data #k p =
  parse_tagged_union_payload_and_then_cases_injective tag_of_data p;
  pt `and_then` parse_tagged_union_payload tag_of_data p

let parse_tagged_union_eq
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (input: bytes)
: Lemma
  (parse (parse_tagged_union pt tag_of_data p) input == (match parse pt input with
  | None -> None
  | Some (tg, consumed_tg) ->
    let input_tg = Seq.slice input consumed_tg (Seq.length input) in
    begin match parse (p tg) input_tg with
    | Some (x, consumed_x) -> Some ((x <: data_t), consumed_tg + consumed_x)
    | None -> None
    end
  ))
= parse_tagged_union_payload_and_then_cases_injective tag_of_data p;
  and_then_eq pt (parse_tagged_union_payload tag_of_data p) input;
  match parse pt input with
  | None -> ()
  | Some (tg, consumed_tg) ->
    let input_tg = Seq.slice input consumed_tg (Seq.length input) in
    parse_synth_eq #k #(refine_with_tag tag_of_data tg) (p tg) (synth_tagged_union_data tag_of_data tg) input_tg

let parse_tagged_union_eq_gen
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (#kt': parser_kind)
  (pt': parser kt' tag_t)
  (lem_pt: (
    (input: bytes) -> 
    Lemma
    (parse pt input == parse pt' input)
  ))
  (k': (t: tag_t) -> Tot parser_kind)
  (p': (t: tag_t) -> Tot (parser (k' t) (refine_with_tag tag_of_data t)))
  (lem_p' : (
    (k: tag_t) ->
    (input: bytes) ->
    Lemma
    (parse (p k) input == parse (p' k) input)
  ))
  (input: bytes)
: Lemma
  (parse (parse_tagged_union pt tag_of_data p) input == bare_parse_tagged_union pt' tag_of_data k' p' input)
= parse_tagged_union_payload_and_then_cases_injective tag_of_data p;
  and_then_eq pt (parse_tagged_union_payload tag_of_data p) input;
  lem_pt input;
  match parse pt input with
  | None -> ()
  | Some (tg, consumed_tg) ->
    let input_tg = Seq.slice input consumed_tg (Seq.length input) in
    parse_synth_eq #k #(refine_with_tag tag_of_data tg) (p tg) (synth_tagged_union_data tag_of_data tg) input_tg;
    lem_p' tg input_tg

let serialize_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Pure (serializer (parse_tagged_union pt tag_of_data p))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= bare_serialize_tagged_union_correct st tag_of_data s;
  bare_serialize_tagged_union st tag_of_data s

let serialize_tagged_union_eq
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
  (input: data_t)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (serialize (serialize_tagged_union st tag_of_data s) input == bare_serialize_tagged_union st tag_of_data s input))
  [SMTPat (serialize (serialize_tagged_union st tag_of_data s) input)]
= ()

let serialize_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
: Tot (serializer (parse_dtuple2 p1 p2))
= serialize_tagged_union
    s1
    dfst
    (fun (x: t1) -> serialize_synth (p2 x) (synth_dtuple2 x) (s2 x) (synth_dtuple2_recip x) ())

let parse_dtuple2_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (p2: (x: t1) -> parser k2 (t2 x))
  (b: bytes)
: Lemma
  (parse (parse_dtuple2 p1 p2) b == (match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse (p2 x1) b' with
    | Some (x2, consumed2) ->
      Some ((| x1, x2 |), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  ))

  by (T.norm [delta_only [`%parse_dtuple2;]])
  
= ()

let serialize_dtuple2_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
  (xy: dtuple2 t1 t2)
: Lemma
  (serialize (serialize_dtuple2 s1 s2) xy == serialize s1 (dfst xy) `Seq.append` serialize (s2 (dfst xy)) (dsnd xy))
= ()

(* Special case for non-dependent parsing *)

let nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (parser (and_then_kind k1 k2) (t1 * t2))
= parse_tagged_union
    p1
    fst
    (fun x -> parse_synth p2 (fun y -> (x, y) <: refine_with_tag fst x))

#set-options "--z3rlimit 16"

let nondep_then_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (b: bytes)
: Lemma
  (parse (nondep_then p1 p2) b == (match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse p2 b' with
    | Some (x2, consumed2) ->
      Some ((x1, x2), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  ))

  by (T.norm [delta_only [`%nondep_then;]])
  
= ()

let serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
: Tot (serializer (nondep_then p1 p2))
= serialize_tagged_union
    s1
    fst
    (fun x -> serialize_synth p2 (fun y -> (x, y) <: refine_with_tag fst x) s2 (fun (xy: refine_with_tag fst x) -> snd xy) ())

let serialize_nondep_then_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: t1 * t2)
: Lemma
  (serialize (serialize_nondep_then s1 s2) input == bare_serialize_nondep_then p1 s1 p2 s2 input)
= ()

let length_serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input1: t1)
  (input2: t2)
: Lemma
  (Seq.length (serialize (serialize_nondep_then s1 s2) (input1, input2)) == Seq.length (serialize s1 input1) + Seq.length (serialize s2 input2))
= ()

let serialize_nondep_then_upd_left
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
: Lemma
  (requires (Seq.length (serialize s1 y) == Seq.length (serialize s1 (fst x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    Seq.length (serialize s1 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_seq s 0 (serialize s1 y)
  ))
= let s = serialize (serialize_nondep_then s1 s2) x in
  seq_upd_seq_left s (serialize s1 y);
  let l1 = Seq.length (serialize s1 (fst x)) in
  Seq.lemma_split s l1;
  Seq.lemma_append_inj (Seq.slice s 0 l1) (Seq.slice s l1 (Seq.length s)) (serialize s1 (fst x)) (serialize s2 (snd x))

let serialize_nondep_then_upd_left_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s1' = serialize s1 (fst x) in
    i' + Seq.length s' <= Seq.length s1' /\
    serialize s1 y == seq_upd_seq s1' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_seq s i' s'
  ))
= serialize_nondep_then_upd_left s1 s2 x y;
  let s = serialize (serialize_nondep_then s1 s2) x in
  let s1' = serialize s1 (fst x) in
  let l1 = Seq.length s1' in
  Seq.lemma_split s l1;
  Seq.lemma_append_inj (Seq.slice s 0 l1) (Seq.slice s l1 (Seq.length s)) s1' (serialize s2 (snd x));
  seq_upd_seq_right_to_left s 0 s1' i' s';
  seq_upd_seq_slice_idem s 0 (Seq.length s1')

let serialize_nondep_then_upd_bw_left
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
: Lemma
  (requires (Seq.length (serialize s1 y) == Seq.length (serialize s1 (fst x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let len2 = Seq.length (serialize s2 (snd x)) in
    len2 + Seq.length (serialize s1 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_bw_seq s len2 (serialize s1 y)
  ))
= serialize_nondep_then_upd_left s1 s2 x y

#reset-options "--z3refresh --z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '* -FStar.Tactis -FStar.Reflection'"

let serialize_nondep_then_upd_bw_left_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s1' = serialize s1 (fst x) in
    i' + Seq.length s' <= Seq.length s1' /\
    serialize s1 y == seq_upd_bw_seq s1' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let len2 = Seq.length (serialize s2 (snd x)) in
    len2 + i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_bw_seq s (len2 + i') s'
  ))
= let j' = Seq.length (serialize s1 (fst x)) - i' - Seq.length s' in
  serialize_nondep_then_upd_left_chain s1 s2 x y j' s';
  assert (j' == Seq.length (serialize (serialize_nondep_then s1 s2) x) - (Seq.length (serialize s2 (snd x)) + i') - Seq.length s')

let serialize_nondep_then_upd_right
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
: Lemma
  (requires (Seq.length (serialize s2 y) == Seq.length (serialize s2 (snd x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    Seq.length (serialize s2 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (fst x, y) == seq_upd_seq s (Seq.length s - Seq.length (serialize s2 y)) (serialize s2 y)
  ))
= let s = serialize (serialize_nondep_then s1 s2) x in
  seq_upd_seq_right s (serialize s2 y);
  let l2 = Seq.length s - Seq.length (serialize s2 (snd x)) in
  Seq.lemma_split s l2;
  Seq.lemma_append_inj (Seq.slice s 0 l2) (Seq.slice s l2 (Seq.length s)) (serialize s1 (fst x)) (serialize s2 (snd x))

let serialize_nondep_then_upd_right_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s2' = serialize s2 (snd x) in
    i' + Seq.length s' <= Seq.length s2' /\
    serialize s2 y == seq_upd_seq s2' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let l1 = Seq.length (serialize s1 (fst x)) in
    Seq.length s == l1 + Seq.length (serialize s2 (snd x)) /\
    l1 + i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (fst x, y) == seq_upd_seq s (l1 + i') s'
  ))
= serialize_nondep_then_upd_right s1 s2 x y;
  let s = serialize (serialize_nondep_then s1 s2) x in
  let s2' = serialize s2 (snd x) in
  let l2 = Seq.length s - Seq.length s2' in
  Seq.lemma_split s l2;
  Seq.lemma_append_inj (Seq.slice s 0 l2) (Seq.slice s l2 (Seq.length s)) (serialize s1 (fst x)) s2';
  seq_upd_seq_right_to_left s l2 s2' i' s';
  seq_upd_seq_slice_idem s l2 (Seq.length s)

#reset-options "--z3rlimit 32 --using_facts_from '* -FStar.Tactis -FStar.Reflection'"


let make_total_constant_size_parser_compose
  (sz: nat)
  (t1 t2: Type)
  (f1: ((s: bytes {Seq.length s == sz}) -> GTot t1))
  (g2: t1 -> GTot t2)
: Lemma
  (requires (
    make_total_constant_size_parser_precond sz t1 f1 /\
    (forall x x' . g2 x == g2 x' ==> x == x')
  ))
  (ensures (
    make_total_constant_size_parser_precond sz t1 f1 /\
    make_total_constant_size_parser_precond sz t2 (f1 `compose` g2) /\
    (forall x x' . {:pattern (g2 x); (g2 x')}  g2 x == g2 x' ==> x == x') /\
    (forall input . {:pattern (parse (make_total_constant_size_parser sz t2 (f1 `compose` g2)) input)} parse (make_total_constant_size_parser sz t2 (f1 `compose` g2)) input == parse (make_total_constant_size_parser sz t1 f1 `parse_synth` g2) input)
  ))
= ()

let parse_filter
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> GTot bool))
: Tot (parser (parse_filter_kind k) (parse_filter_refine f))
= p `and_then` (parse_filter_payload f)

let parse_filter_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: bytes)
: Lemma
  (parse (parse_filter p f) input == (match parse p input with
  | None -> None
  | Some (x, consumed) ->
    if f x
    then Some (x, consumed)
    else None
  ))
= ()

let serialize_filter_correct
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Lemma
  (serializer_correct (parse_filter p f) (serialize_filter' s f))
= ()
