module LowParse.Spec.Recursive

open LowParse.Spec.Fuel

module Seq = FStar.Seq

let parse_recursive_aux_ext
  (p: parse_recursive_param)
  (ih1 ih2: tot_parser (parse_recursive_kind p.parse_header_kind) p.t)
  (b: bytes)
  (prf: (
    (b': bytes { Seq.length b' < Seq.length b }) -> // IMPORTANT: lt, not leq, to make induction work
    Lemma
    (parse ih1 b' == parse ih2 b')
  ))
: Lemma
  (parse (parse_recursive_aux p ih1) b == parse (parse_recursive_aux p ih2) b)
= p.synth_inj;
  tot_parse_synth_eq (parse_recursive_alt p ih1) p.synth_ b;
  tot_parse_synth_eq (parse_recursive_alt p ih2) p.synth_ b;
  match parse p.parse_header b with
  | None -> ()
  | Some (h, consumed) ->
    parser_kind_prop_equiv p.parse_header_kind p.parse_header;
    let b' = Seq.slice b consumed (Seq.length b) in
    tot_parse_nlist_parse_nlist (p.count h) ih1 b';
    tot_parse_nlist_parse_nlist (p.count h) ih2 b';
    parse_nlist_ext
      (p.count h)
      #(parse_recursive_kind p.parse_header_kind)
      ih1
      #(parse_recursive_kind p.parse_header_kind)
      ih2
      b'
      (fun b'' -> prf b'')

let rec parse_recursive_step
  (p: parse_recursive_param)
  (n: nat)
: Tot (tot_parser (parse_recursive_kind p.parse_header_kind) p.t)
= if n = 0
  then tot_fail_parser _ _
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
  p
= (tot_close_by_fuel (parse_recursive_step p) closure (parse_recursive_step_ext p))

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

#push-options "--z3rlimit 32"

#restart-solver
let parse_consume_nlist_recursive_eq'
  (p: parse_recursive_param)
  (n: nat)
  (b: bytes)
: Lemma
  (parse_consume (tot_parse_nlist n (parse_recursive p)) b == begin
    if n = 0
    then Some (0)
    else match parse p.parse_header b with
    | None -> None
    | Some (h, consumed1) ->
      let b2 = Seq.slice b consumed1 (Seq.length b) in
      match parse_consume (tot_parse_nlist (p.count h + (n - 1)) (parse_recursive p)) b2 with
      | None -> None
      | Some (consumed2) ->
        Some (consumed1 + consumed2)
  end
  )
= tot_parse_nlist_eq n (parse_recursive p) b;
  if n = 0
  then ()
  else begin
    parse_recursive_eq' p b;
    match parse p.parse_header b with
    | None -> ()
    | Some (h, consumed1) ->
      let b2 = Seq.slice b consumed1 (Seq.length b) in
      tot_parse_nlist_sum (parse_recursive p) (p.count h) (n - 1) b2
  end

#pop-options


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
  (s: tot_serializer #(parse_filter_kind (and_then_kind pp.parse_header_kind parse_recursive_payload_kind)) (tot_parse_filter (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n)))
: Tot (tot_serializer #(parse_filter_kind (parse_recursive_kind pp.parse_header_kind)) (tot_parse_filter (parse_recursive pp) (has_level sp.level n)))
= let s'
    (x: parse_filter_refine (has_level sp.level n))
  : Tot bytes
  = level_correct' sp n x;
    s (sp.synth_recip x)
  in
  mk_tot_serializer
    _
    s'
    (fun x ->
      let b = s' x in
      level_correct' sp n x;
      tot_parse_filter_eq (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n) b;
      tot_parse_filter_eq (parse_recursive pp) (has_level sp.level n) b;
      parse_recursive_eq pp b;
      pp.synth_inj;
      tot_parse_synth_eq (parse_recursive_alt pp (parse_recursive pp)) pp.synth_ b
    )

let mk_serialize_recursive_alt_with_level
  (#pp: parse_recursive_param)
  (#sp: serialize_recursive_param pp)
  (n: nat)
  (s: ((l: pp.header) -> tot_serializer #parse_recursive_payload_kind (tot_weaken parse_recursive_payload_kind (tot_parse_nlist (pp.count l) (parse_recursive pp) `tot_parse_filter` list_has_pred_level sp.level n))))
: Tot (tot_serializer #(parse_filter_kind (and_then_kind pp.parse_header_kind parse_recursive_payload_kind)) #(parse_filter_refine #(parse_recursive_alt_t pp.t pp.header pp.count) (has_pred_level #pp sp n)) (tot_parse_filter #_ #(parse_recursive_alt_t pp.t pp.header pp.count) (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n)))
= let s1 = tot_serialize_dtuple2 sp.serialize_header s in
  let s'
    (x: parse_filter_refine (has_pred_level sp n))
  = let (| l, c |) = x in
    s1 (| l, c |)
  in
  mk_tot_serializer
//    #(parse_filter_kind (and_then_kind pp.parse_header_kind parse_recursive_payload_kind))
//    #(parse_filter_refine #(parse_recursive_alt_t pp.t pp.header pp.count) (has_pred_level #pp sp n))
  (tot_parse_filter #_ #(parse_recursive_alt_t pp.t pp.header pp.count) (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n))
    s'
    (fun x ->
      let b = s' x in
      tot_parse_dtuple2_ext
        pp.parse_header
        pp.parse_header
        (fun l ->
          tot_weaken parse_recursive_payload_kind (tot_parse_nlist (pp.count l) (parse_recursive pp) `tot_parse_filter` list_has_pred_level sp.level n)
        )
        (fun l ->
          tot_weaken parse_recursive_payload_kind (tot_parse_nlist (pp.count l) (parse_recursive pp)) `tot_parse_filter` list_has_pred_level sp.level n
        )
        b
        ()
        (fun l b' ->
          tot_parse_filter_eq
            (tot_parse_nlist (pp.count l) (parse_recursive pp))
            (list_has_pred_level sp.level n)
            b';
          tot_parse_filter_eq
            (tot_weaken parse_recursive_payload_kind (tot_parse_nlist (pp.count l) (parse_recursive pp)))
            (list_has_pred_level sp.level n)
            b'
        );
      tot_parse_dtuple2_filter_swap
        pp.parse_header
        (parse_recursive_payload pp (parse_recursive pp))
        (fun _ -> list_has_pred_level sp.level n)
        (fun l -> tot_weaken parse_recursive_payload_kind (tot_parse_nlist (pp.count l) (parse_recursive pp)) `tot_parse_filter` list_has_pred_level sp.level n)
        (has_pred_level sp n)
        b;
      tot_parse_filter_eq (parse_recursive_alt pp (parse_recursive pp)) (has_pred_level sp n) b;
      assert (Some? (parse (parse_recursive_alt pp (parse_recursive pp)) b));
      let Some (l, consumed) = parse pp.parse_header b in
      let b' = Seq.slice b consumed (Seq.length b) in
      tot_parse_filter_eq (tot_parse_nlist (pp.count l) (parse_recursive pp)) (list_has_pred_level sp.level n) b'
    )

let serialize_recursive_list_has_pred_level_zero
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (n: nat { n == 0 })
  (len: nat)
: tot_serializer (tot_parse_nlist len (parse_recursive pp) `tot_parse_filter` list_has_pred_level sp.level n)
= let s' : tot_bare_serializer (parse_filter_refine #(nlist len pp.t) (list_has_pred_level sp.level n)) = fun _ -> Seq.empty in
  mk_tot_serializer
    _
    s'
    (fun x ->
      assert (Nil? x);
      let res : bytes = Seq.empty in
      tot_parse_filter_eq (tot_parse_nlist len (parse_recursive pp)) (list_has_pred_level sp.level n) res;
      tot_parse_nlist_eq n (parse_recursive pp) res
    )

#restart-solver

let serialize_recursive_list_has_pred_level_pos
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (n: pos)
  (s: tot_serializer (tot_parse_filter (parse_recursive pp) (has_level sp.level (n - 1))))
  (len: nat)
: Tot (tot_serializer (tot_parse_nlist len (parse_recursive pp) `tot_parse_filter` list_has_pred_level sp.level n))
  (decreases len)
= Classical.forall_intro (forall_list_correct (has_level sp.level (n - 1)));
  tot_serialize_refine_nlist (parse_recursive pp) (has_level sp.level (n - 1)) (list_has_pred_level sp.level n) s len

let rec serialize_recursive_with_level
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (n: nat)
: Tot (tot_serializer (tot_parse_filter (parse_recursive pp) (has_level sp.level n)))
= mk_serialize_recursive_with_level
    n
    (mk_serialize_recursive_alt_with_level
      n
      (fun l ->
        let len = pp.count l in
        tot_serialize_weaken _
        (
          if n = 0
          then serialize_recursive_list_has_pred_level_zero sp n len
          else serialize_recursive_list_has_pred_level_pos sp n (serialize_recursive_with_level sp (n - 1)) len
        )
      )
    )

let serialize_recursive
  #pp sp
= let s' (x: pp.t) : Tot bytes =
    serialize_recursive_with_level sp (sp.level x) x
  in
  mk_tot_serializer
    _
    s'
    (fun x ->
      tot_parse_filter_eq (parse_recursive pp) (has_level sp.level (sp.level x)) (s' x)
    )

let serialize_recursive_eq
  #pp sp x
=
  Classical.forall_intro (parse_recursive_eq pp);
  let s' = tot_serialize_ext (parse_recursive pp) (serialize_recursive sp) (parse_recursive_aux pp (parse_recursive pp)) in
  serializer_unique #(parse_recursive_kind pp.parse_header_kind) (parse_recursive pp) (serialize_recursive_aux sp) s' x
