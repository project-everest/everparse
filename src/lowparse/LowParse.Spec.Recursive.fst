module LowParse.Spec.Recursive

open LowParse.Spec.Fuel

module Seq = FStar.Seq

let parse_recursive_aux_ext
  (p: parse_recursive_param)
  (ih1 ih2: parser (parse_recursive_kind p.parse_header_kind) p.t)
  (b: bytes)
  (prf: (
    (b': bytes { Seq.length b' < Seq.length b }) -> // IMPORTANT: lt, not leq, to make induction work
    Lemma
    (parse ih1 b' == parse ih2 b')
  ))
: Lemma
  (parse (parse_recursive_aux p ih1) b == parse (parse_recursive_aux p ih2) b)
= p.synth_inj;
  parse_synth_eq (parse_recursive_alt p ih1) p.synth_ b;
  parse_synth_eq (parse_recursive_alt p ih2) p.synth_ b;
  parse_dtuple2_eq p.parse_header (parse_recursive_payload p ih1) b;
  parse_dtuple2_eq p.parse_header (parse_recursive_payload p ih2) b;
  match parse p.parse_header b with
  | None -> ()
  | Some (h, consumed) ->
    parser_kind_prop_equiv p.parse_header_kind p.parse_header;
    let b' = Seq.slice b consumed (Seq.length b) in
    parse_nlist_ext
      (p.count h)
      ih1
      ih2
      b'
      (fun b'' -> prf b'')

let rec parse_recursive_step
  (p: parse_recursive_param)
  (n: nat)
: Tot (parser (parse_recursive_kind p.parse_header_kind) p.t)
= if n = 0
  then fail_parser _ _
  else parse_recursive_aux p (parse_recursive_step p (n - 1))

let closure
  (b: bytes)
: Tot (n: nat { Seq.length b < n })
= Seq.length b + 1

let rec parse_recursive_step_ext_gen
  (p: parse_recursive_param)
  (fuel: nat)
  (fuel': nat { fuel <= fuel' })
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_recursive_step p fuel) input == parse (parse_recursive_step p fuel') input))
  (decreases fuel)
= parse_recursive_aux_ext
    p
    (parse_recursive_step p (fuel - 1))
    (parse_recursive_step p (fuel' - 1))
    input
    (fun input' ->
      parse_recursive_step_ext_gen p (fuel - 1) (fuel' - 1) input'
    )

let parse_recursive_step_ext
  (p: parse_recursive_param)
  (fuel: nat)
  (input: bytes { Seq.length input < fuel })
: Lemma
  (ensures (parse (parse_recursive_step p fuel) input == parse (parse_recursive_step p (closure input)) input))
= parse_recursive_step_ext_gen p (closure input) fuel input

let parse_recursive
  (p: parse_recursive_param)
: Tot (parser (parse_recursive_kind p.parse_header_kind) p.t)
= close_by_fuel (parse_recursive_step p) closure (parse_recursive_step_ext p)

let parse_recursive_eq
  (p: parse_recursive_param)
  (b: bytes)
: Lemma
  (parse (parse_recursive p) b == parse (parse_recursive_aux p (parse_recursive p)) b)
= let c = closure b in
  let q = parse_recursive_step p (c - 1) in
  assert (parse (parse_recursive p) b == parse (parse_recursive_aux p q) b);
  parse_recursive_aux_ext p q (parse_recursive p) b (fun input' -> // here hypothesis Seq.length input' < Seq.length input is used
    parse_recursive_step_ext p (c - 1) input'
  )

let has_pred_level
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: nat)
  (x: (h: p.header & nlist (p.count h) p.t))
: Tot bool
= list_has_pred_level s.level n (dsnd x)

let level_correct'
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: nat)
  (x: parse_filter_refine (has_level s.level n))
: Lemma
  (has_pred_level s n (s.synth_recip x))
= s.level_correct x n

let mk_serialize_recursive_with_level
  (#pp: parse_recursive_param)
  (#sp: serialize_recursive_param pp)
  (n: nat)
  (s: serializer (parse_filter (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n)))
: Tot (serializer (parse_filter (parse_recursive pp) (has_level sp.level n)))
= let s'
    (x: parse_filter_refine (has_level sp.level n))
  : GTot bytes
  = level_correct' sp n x;
    s (sp.synth_recip x)
  in
  mk_serializer
    _
    s'
    (fun x ->
      let b = s' x in
      level_correct' sp n x;
      parse_filter_eq (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n) b;
      parse_filter_eq (parse_recursive pp) (has_level sp.level n) b;
      parse_recursive_eq pp b;
      pp.synth_inj;
      parse_synth_eq (parse_recursive_alt pp (parse_recursive pp)) pp.synth_ b
    )

let mk_serialize_recursive_alt_with_level
  (#pp: parse_recursive_param)
  (#sp: serialize_recursive_param pp)
  (n: nat)
  (s: ((l: pp.header) -> serializer (weaken parse_recursive_payload_kind (parse_nlist (pp.count l) (parse_recursive pp) `parse_filter` list_has_pred_level sp.level n))))
: Tot (serializer (parse_filter (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n)))
= let s1 = serialize_dtuple2 sp.serialize_header s in
  let s'
    (x: parse_filter_refine (has_pred_level sp n))
  = let (| l, c |) = x in
    s1 (| l, c |)
  in
  mk_serializer
    _
    s'
    (fun x ->
      let b = s' x in
      parse_filter_eq (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n) b;
      parse_dtuple2_eq pp.parse_header (parse_recursive_payload pp (parse_recursive pp)) b;
      parse_dtuple2_eq pp.parse_header (fun l -> weaken parse_recursive_payload_kind (parse_nlist (pp.count l) (parse_recursive pp) `parse_filter` list_has_pred_level sp.level n)) b;
      let Some (l, consumed) = parse pp.parse_header b in
      let b' = Seq.slice b consumed (Seq.length b) in
      parse_filter_eq (parse_nlist (pp.count l) (parse_recursive pp)) (list_has_pred_level sp.level n) b'
    )

let serialize_recursive_list_has_pred_level_zero
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (n: nat { n == 0 })
  (len: nat)
: serializer (parse_nlist len (parse_recursive pp) `parse_filter` list_has_pred_level sp.level n)
= let s' : bare_serializer (parse_filter_refine #(nlist len pp.t) (list_has_pred_level sp.level n)) = fun _ -> Seq.empty in
  mk_serializer
    _
    s'
    (fun x ->
      assert (Nil? x);
      let res : bytes = Seq.empty in
      parse_filter_eq (parse_nlist len (parse_recursive pp)) (list_has_pred_level sp.level n) res;
      parse_nlist_eq n (parse_recursive pp) res
    )

#restart-solver

let rec serialize_recursive_list_has_pred_level_pos
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (n: pos)
  (s: serializer (parse_filter (parse_recursive pp) (has_level sp.level (n - 1))))
  (len: nat)
: Tot (serializer (parse_nlist len (parse_recursive pp) `parse_filter` list_has_pred_level sp.level n))
  (decreases len)
= let s'
    (l: parse_filter_refine #(nlist len pp.t) (list_has_pred_level sp.level n))
  : GTot bytes
  = match l with
    | [] -> Seq.empty
    | a :: q ->
      forall_list_cons a q (has_level sp.level (n - 1));
      s a `Seq.append` serialize_recursive_list_has_pred_level_pos sp n s (len - 1) q
  in
  mk_serializer
    (parse_nlist len (parse_recursive pp) `parse_filter` list_has_pred_level sp.level n)
    s'
    (fun l ->
      let b = s' l in
      parse_filter_eq (parse_nlist len (parse_recursive pp)) (list_has_pred_level sp.level n) b;
      parse_nlist_eq len (parse_recursive pp) b;
      match l with
      | [] -> ()
      | a :: q ->
        forall_list_cons a q (has_level sp.level (n - 1));
        parse_filter_eq (parse_recursive pp) (has_level sp.level (n - 1)) (s a);
        let b' = serialize_recursive_list_has_pred_level_pos sp n s (len - 1) q in
        assert_norm (s' (a :: q) == s a `Seq.append` b');
        assert (parse (parse_recursive pp) (s a) == Some (a, Seq.length (s a)));
        let (b1, b2) = Seq.split_eq b (Seq.length (s a)) in
        Seq.lemma_append_inj b1 b2 (s a) b';
        parse_strong_prefix (parse_recursive pp) (s a) b;
        parse_filter_eq (parse_nlist (len - 1) (parse_recursive pp)) (list_has_pred_level sp.level n) b'
    )

let rec serialize_recursive_with_level
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (n: nat)
: Tot (serializer (parse_filter (parse_recursive pp) (has_level sp.level n)))
= mk_serialize_recursive_with_level
    n
    (mk_serialize_recursive_alt_with_level
      n
      (fun l ->
        let len = pp.count l in
        serialize_weaken _
        (
          if n = 0
          then serialize_recursive_list_has_pred_level_zero sp n len
          else serialize_recursive_list_has_pred_level_pos sp n (serialize_recursive_with_level sp (n - 1)) len
        )
      )
    )

let serialize_recursive
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
: Tot (serializer (parse_recursive pp))
=
  let s' (x: pp.t) : GTot bytes =
    serialize_recursive_with_level sp (sp.level x) x
  in
  mk_serializer
    _
    s'
    (fun x ->
      parse_filter_eq (parse_recursive pp) (has_level sp.level (sp.level x)) (s' x)
    )

let serialize_recursive_eq
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (x: pp.t)
: Lemma
  (serialize (serialize_recursive sp) x == serialize (serialize_recursive_aux sp) x)
=
  Classical.forall_intro (parse_recursive_eq pp);
  let s' = serialize_ext (parse_recursive pp) (serialize_recursive sp) (parse_recursive_aux pp (parse_recursive pp)) in
  serializer_unique _ (serialize_recursive_aux sp) s' x
