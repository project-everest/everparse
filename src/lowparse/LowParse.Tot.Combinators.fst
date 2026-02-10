module LowParse.Tot.Combinators
include LowParse.Spec.Combinators
include LowParse.Tot.Base

inline_for_extraction
let fail_parser = tot_fail_parser

inline_for_extraction
let parse_ret = tot_parse_ret

inline_for_extraction
let parse_empty : parser parse_ret_kind unit =
  parse_ret ()

inline_for_extraction
let parse_synth #k #t1 #t2 = tot_parse_synth #k #t1 #t2

val parse_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (b: bytes)
: Lemma
  (requires (k.parser_kind_injective ==> synth_injective f2))
  (ensures (parse (parse_synth p1 f2) b == parse_synth' #k p1 f2 b))

let parse_synth_eq #k #t1 #t2 = tot_parse_synth_eq #k #t1 #t2

val serialize_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: tot_parser k t1)
  (f2: t1 -> Tot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer (tot_parse_synth p1 f2))

let serialize_synth #k #t1 #t2 = serialize_tot_synth #k #t1 #t2

let serialize_weaken
  (#k: parser_kind)
  (#t: Type)
  (k' : parser_kind)
  (#p: parser k t)
  (s: serializer p { k' `is_weaker_than` k /\ k'.parser_kind_injective == true })
: Tot (serializer (weaken k' p))
= serialize_weaken #k k' s

inline_for_extraction
let parse_filter #k #t = tot_parse_filter #k #t

val parse_filter_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> Tot bool))
  (input: bytes)
: Lemma
  (parse (parse_filter p f) input == (match parse p input with
  | None -> None
  | Some (x, consumed) ->
    if f x
    then Some (x, consumed)
    else None
  ))

let parse_filter_eq #k #t = tot_parse_filter_eq #k #t

let serialize_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> Tot bool))
: Tot (serializer (parse_filter p f))
= Classical.forall_intro (parse_filter_eq #k #t p f);
  serialize_ext _ (serialize_filter s f) _

inline_for_extraction
let and_then #k #t = tot_and_then #k #t

val and_then_eq
  (#k: parser_kind)
  (#t:Type)
  (p: parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
  (input: bytes)
: Lemma
  (requires ((and_then_kind k k').parser_kind_injective ==> and_then_cases_injective p'))
  (ensures (parse (and_then p p') input == and_then_bare p p' input))

let and_then_eq #k #t p #k' #t' p' input = and_then_eq #k #t p #k' #t' p' input

inline_for_extraction
val parse_tagged_union_payload
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> Tot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (tg: tag_t)
: Tot (parser k data_t)

let parse_tagged_union_payload #tag_t #data_t = tot_parse_tagged_union_payload #tag_t #data_t

inline_for_extraction
val parse_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> Tot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Tot (parser (and_then_kind kt k) data_t)

let parse_tagged_union #kt #tag_t = tot_parse_tagged_union #kt #tag_t

let parse_tagged_union_payload_and_then_cases_injective
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> Tot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Lemma
  (and_then_cases_injective (parse_tagged_union_payload tag_of_data p))
= parse_tagged_union_payload_and_then_cases_injective tag_of_data #k p

val parse_tagged_union_eq
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> Tot tag_t))
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

let parse_tagged_union_eq #kt #tag_t pt #data_t tag_of_data #k p input =
  parse_tagged_union_eq #kt #tag_t pt #data_t tag_of_data #k p input

val serialize_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> Tot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Pure (serializer (parse_tagged_union pt tag_of_data p))
  (requires (kt.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_injective == true))
  (ensures (fun _ -> True))

let serialize_tagged_union #kt st tag_of_data #k s = serialize_tot_tagged_union #kt st tag_of_data #k s

val nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (parser (and_then_kind k1 k2) (t1 * t2))

let nondep_then #k1 = tot_nondep_then #k1

val nondep_then_eq
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

let nondep_then_eq #k1 #t1 p1 #k2 #t2 p2 b =
  nondep_then_eq #k1 p1 #k2 p2 b

let make_constant_size_parser
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> Tot (option t)))
: Pure (
    tot_parser
      (constant_size_parser_kind sz)
      t
  )
  (requires (
    make_constant_size_parser_precond sz t f
  ))
  (ensures (fun _ -> True))
= tot_make_constant_size_parser sz t f
