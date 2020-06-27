module LowParseWriters.Compat

friend LowParseWriters.LowParse
friend LowParseWriters.Parsers

module B = LowStar.Buffer

let star_correct
  p1 p2
= ()

let parse_synth
  p1 #t2 f2 f1
= make_parser
    ((dsnd p1).parser `LP.parse_synth` f2)
    (LP.serialize_synth (dsnd p1).parser f2 (dsnd p1).serializer f1 ())
    (LP.jump_synth (dsnd p1).jumper f2 ())

let valid_synth_parse_synth
  p1 #t2 f2 f1 sq
= {
  valid_synth_valid = (fun h b pos pos' ->
    LP.valid_synth h (get_parser p1) f2 (LP.make_slice b (B.len b)) pos
  );
  valid_synth_size = (fun x ->
    LP.synth_injective_synth_inverse_synth_inverse_recip f2 f1 ();
    LP.serialize_synth_eq (get_parser p1) f2 (dsnd p1).serializer f1 () (f2 x)
  );
}

let valid_synth_parse_synth_recip
  p1 #t2 f2 f1 sq
= {
  valid_synth_valid = (fun h b pos pos' ->
    LP.synth_injective_synth_inverse_synth_inverse_recip f2 f1 ();
    LP.valid_synth h (get_parser p1) f2 (LP.make_slice b (B.len b)) pos
  );
  valid_synth_size = (fun x ->
    LP.serialize_synth_eq (get_parser p1) f2 (dsnd p1).serializer f1 () (x)
  );
}

let parse_vldata_correct
  p min max
= ()

let list_size_correct
  p x
= ()

let parse_vllist_correct
  p min max
= ()

let parse_vlbytes_correct
  min max
= ()

let parse_enum
  #key p e
=
  make_parser
    (LP.parse_enum_key (get_parser p) e)
    (LP.serialize_enum_key _ (get_serializer p) e)
    (LP.jump_enum_key (dsnd p).jumper e)

let rec glb_list_of_strong
  (#t: eqtype)
  (f: (t -> Tot LP.parser_kind))
  (l: list t)
  (f_strong: ((x: t) -> Lemma (List.Tot.mem x l ==> (f x).LP.parser_kind_subkind == Some LP.ParserStrong)))
: Lemma
  (requires (Cons? l))
  (ensures ((LP.glb_list_of f l).LP.parser_kind_subkind == Some LP.ParserStrong))
= match l with
  | [a] ->
    f_strong a
  | a :: q ->
    f_strong a;
    glb_list_of_strong f q f_strong

let weaken_parse_cases_kind_strong_parser_kind
  (s: LP.sum { Cons? (LP.Sum?.e s) })
  (f: (x: LP.sum_key s) -> Tot (k: LP.parser_kind & LP.parser k (LP.sum_type_of_tag s x)))
  (f_strong: (x: LP.sum_key s) -> Lemma ((dfst (f x)).LP.parser_kind_subkind == Some LP.ParserStrong))
: Lemma
  ((LP.weaken_parse_cases_kind s f).LP.parser_kind_subkind == Some LP.ParserStrong)
=
  let keys : list (LP.sum_key_type s) = List.Tot.map fst (LP.sum_enum s) in
  glb_list_of_strong #(LP.sum_key_type s) (fun (x: LP.sum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else LP.default_parser_kind
  ) (List.Tot.map fst (LP.sum_enum s))
  (fun x ->
    if List.Tot.mem x keys
    then f_strong x
    else ()
  )

let parse_sum_kind_strong
  (ps: parse_sum_t)
: Lemma
  ((LP.parse_sum_kind ps.sum_kt ps.sum_t ps.sum_pc).LP.parser_kind_subkind == Some LP.ParserStrong)
= weaken_parse_cases_kind_strong_parser_kind ps.sum_t ps.sum_pc (fun x -> let p = ps.sum_pc' x in ())
  
let parse_sum
  ps
=
  [@inline_let]
  let _ = parse_sum_kind_strong ps in
  make_parser
    (LP.parse_sum ps.sum_t ps.sum_p ps.sum_pc)
    (LP.serialize_sum #ps.sum_kt ps.sum_t #ps.sum_p ps.sum_s #ps.sum_pc ps.sum_sc)
    (LP.jump_sum ps.sum_t (dsnd (ps.sum_p')).jumper ps.sum_r ps.sum_pc (fun x -> (dsnd (ps.sum_pc' x)).jumper) ps.sum_destr)

let valid_synth_parse_sum
  ps k
= {
  valid_synth_valid = (fun h b pos pos' ->
    let sl = LP.make_slice b (B.len b) in
    assert (LP.valid (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t) `LP.nondep_then` dsnd (ps.sum_pc k)) h sl pos);
    let (k', _) = LP.contents (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t) `LP.nondep_then` dsnd (ps.sum_pc k)) h sl pos in
    assert (k' == k);
    LP.valid_nondep_then h (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t)) (dsnd (ps.sum_pc k)) sl pos;
    assert (LP.valid (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t)) h sl pos);
    assert (LP.contents (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t)) h sl pos == k);
    LP.valid_sum_intro h ps.sum_t ps.sum_p ps.sum_pc sl pos
  );
  valid_synth_size = (fun x ->
    let (k', pl) = LP.coerce (dfst (parse_enum ps.sum_p' (LP.sum_enum ps.sum_t)) & dfst (ps.sum_pc' k)) (x <: (dfst (parse_enum ps.sum_p' (LP.sum_enum ps.sum_t) `star` ps.sum_pc' k))) in
    let y = LP.synth_sum_case ps.sum_t k pl in
    assert (LP.sum_tag_of_data ps.sum_t y == k);
    LP.synth_sum_case_inverse ps.sum_t k;
    LP.synth_sum_case_injective ps.sum_t k;
    LP.synth_injective_synth_inverse_synth_inverse_recip (LP.synth_sum_case ps.sum_t k) (LP.synth_sum_case_recip ps.sum_t k) ();
    assert (LP.synth_sum_case_recip ps.sum_t k y == pl);
    LP.serialize_sum_eq ps.sum_t ps.sum_s #ps.sum_pc ps.sum_sc y
  );
}
