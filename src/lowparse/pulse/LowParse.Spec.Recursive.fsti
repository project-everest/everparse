module LowParse.Spec.Recursive

open LowParse.Spec.Combinators
open LowParse.Spec.VCList
open LowParse.WellFounded

module Seq = FStar.Seq

let parse_recursive_payload_t
  (t: Type)
  (header: Type)
  (count: (header -> nat))
  (h: header)
: Tot Type
= nlist (count h) t

let parse_recursive_alt_t
  (t: Type)
  (header: Type)
  (count: (header -> nat))
: Tot Type
= dtuple2 header (parse_recursive_payload_t t header count)

[@@(noextract_to "krml")]
inline_for_extraction
noeq
type parse_recursive_param = {
  t: Type;
  header: Type;
  parse_header_kind: (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 });
  parse_header: tot_parser parse_header_kind header;
  count: (header -> nat);
  synth_: (parse_recursive_alt_t t header count -> t);
  synth_inj: squash (synth_injective synth_);
}

let parse_recursive_kind
  (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })
: Tot parser_kind
= {
    parser_kind_low = k.parser_kind_low;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None;
  }

let parse_recursive_payload_kind
: parser_kind
= {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None;
  }

let parse_recursive_payload
  (p: parse_recursive_param)
  (ih: tot_parser (parse_recursive_kind p.parse_header_kind) p.t)
  (h: p.header)
: Tot (tot_parser parse_recursive_payload_kind (parse_recursive_payload_t p.t p.header p.count h))
= tot_weaken parse_recursive_payload_kind (tot_parse_nlist (p.count h) ih)

let parse_recursive_alt
  (p: parse_recursive_param)
  (ih: tot_parser (parse_recursive_kind p.parse_header_kind) p.t)
: Tot (tot_parser _ (parse_recursive_alt_t p.t p.header p.count))
= p.parse_header `tot_parse_dtuple2` parse_recursive_payload p ih

let parse_recursive_aux
  (p: parse_recursive_param)
  (ih: tot_parser (parse_recursive_kind p.parse_header_kind) p.t)
: Tot (tot_parser (parse_recursive_kind p.parse_header_kind) p.t)
= tot_weaken _ (parse_recursive_alt p ih `tot_parse_synth` p.synth_)

val parse_recursive
  (p: parse_recursive_param)
: Tot (tot_parser (parse_recursive_kind p.parse_header_kind) p.t)

val parse_recursive_eq
  (p: parse_recursive_param)
  (b: bytes)
: Lemma
  (parse (parse_recursive p) b == parse (parse_recursive_aux p (parse_recursive p)) b)

let parse_recursive_eq'
  (p: parse_recursive_param)
  (b: bytes)
: Lemma
  (parse (parse_recursive p) b == begin match parse p.parse_header b with
  | None -> None
  | Some (h, consumed1) ->
    let b2 = Seq.slice b consumed1 (Seq.length b) in
    match parse (tot_parse_nlist (p.count h) (parse_recursive p)) b2 with
    | None -> None
    | Some (l, consumed2) ->
      Some (p.synth_ (| h, l |), consumed1 + consumed2)
  end
  )
= parse_recursive_eq p b;
  tot_parse_synth_eq (parse_recursive_alt p (parse_recursive p)) p.synth_ b

let spec_parse_recursive_payload
  (p: parse_recursive_param)
  (ih: parser (parse_recursive_kind p.parse_header_kind) p.t)
  (h: p.header)
: Tot (parser parse_recursive_payload_kind (parse_recursive_payload_t p.t p.header p.count h))
= weaken parse_recursive_payload_kind (parse_nlist (p.count h) ih)

let spec_parse_recursive_aux
  (p: parse_recursive_param)
  (#k: parser_kind)
  (ph: parser k p.header)
  (ih: parser (parse_recursive_kind p.parse_header_kind) p.t)
: Tot (parser _ p.t)
= (ph `parse_dtuple2` spec_parse_recursive_payload p ih) `parse_synth` p.synth_

let parse_recursive_eq_gen
  (p: parse_recursive_param)
  (k: parser_kind)
  (ph: parser k p.header)
: Lemma
  (requires (forall b . parse ph b == parse p.parse_header b))
  (ensures (forall b. parse (parse_recursive p) b == parse (spec_parse_recursive_aux p ph (parser_of_tot_parser (parse_recursive p))) b))
= let prf
    (b: bytes)
  : Lemma (parse (parse_recursive p) b == parse (spec_parse_recursive_aux p ph (parser_of_tot_parser (parse_recursive p))) b)
  = let ih = (parser_of_tot_parser (parse_recursive p)) in
    parse_recursive_eq' p b;
    parse_synth_eq
      (parse_dtuple2 ph (spec_parse_recursive_payload p ih))
      p.synth_
      b;
    parse_dtuple2_eq ph (spec_parse_recursive_payload p ih) b;
    match parse ph b with
    | None -> ()
    | Some (h, lenh) ->
      let b' = Seq.slice b lenh (Seq.length b) in
      tot_parse_nlist_parse_nlist (p.count h) (parse_recursive p) b';
      ()
  in
  Classical.forall_intro prf

let tot_parse_nlist_sum
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (n1 n2: nat)
  (b: bytes)
: Lemma
  (ensures (parse (tot_parse_nlist (n1 + n2) p) b ==
    begin match parse (tot_parse_nlist n1 p) b with
    | None -> None
    | Some (l1, consumed1) ->
      let b2 = Seq.slice b consumed1 (Seq.length b) in
      match parse (tot_parse_nlist n2 p) b2 with
      | None -> None
      | Some (l2, consumed2) ->
        List.Tot.append_length l1 l2;
        Some (l1 `List.Tot.append` l2, consumed1 + consumed2)
    end
  ))
= Classical.forall_intro_2 (fun n -> tot_parse_nlist_parse_nlist n p);
  parse_nlist_sum #k #t p n1 n2 b

val parse_consume_nlist_recursive_eq'
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

let list_has_pred_level
  (#t: Type)
  (level: (t -> nat))
  (n: nat)
  (l: list t)
: Tot bool
= if n = 0 then Nil? l else forall_list l (has_level level (n - 1))

[@@(noextract_to "krml")]
inline_for_extraction
noeq
type serialize_recursive_param (p: parse_recursive_param) = {
  serialize_header: tot_serializer #p.parse_header_kind p.parse_header;
  synth_recip: (p.t -> (parse_recursive_alt_t p.t p.header p.count));
  synth_inv: squash (synth_inverse p.synth_ synth_recip);
  level: (p.t -> nat);
  level_correct: (x: p.t) -> (n: nat) -> Lemma (requires (has_level level n x)) (ensures ( (list_has_pred_level level n (dsnd (synth_recip x)))));
}

val serialize_recursive
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
: Tot (tot_serializer #(parse_recursive_kind pp.parse_header_kind) (parse_recursive pp))

let serialize_recursive_payload
  (#p: parse_recursive_param)
  (sp: serialize_recursive_param p)
  (h: p.header)
: Tot (tot_serializer (parse_recursive_payload p (parse_recursive p) h))
= tot_serialize_weaken _
    (tot_serialize_nlist
      (p.count h)
      (serialize_recursive sp)
    )

let serialize_recursive_aux
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
: Tot (tot_serializer (parse_recursive_aux pp (parse_recursive pp)))
=
  tot_serialize_weaken _
    (tot_serialize_synth _
      pp.synth_
      (tot_serialize_dtuple2
        sp.serialize_header
        (serialize_recursive_payload sp)
      )
      sp.synth_recip
      ()
    )

val serialize_recursive_eq
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (x: pp.t)
: Lemma
  (bare_serialize (serialize_recursive sp) x == bare_serialize (serialize_recursive_aux sp) x)

let spec_serialize_recursive_payload
  (#p: parse_recursive_param)
  (sp: serialize_recursive_param p)
  (h: p.header)
: Tot (serializer (spec_parse_recursive_payload p (parse_recursive p) h))
= serialize_weaken _
    (serialize_nlist
      (p.count h)
      (serialize_recursive sp)
    )

let spec_serialize_recursive_aux
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (#k: parser_kind)
  (#ph: parser k pp.header)
  (sh: serializer ph { k.parser_kind_subkind == Some ParserStrong })
: Tot (serializer (spec_parse_recursive_aux pp ph (parse_recursive pp)))
=
  serialize_weaken _
    (serialize_synth _
      pp.synth_
      (serialize_dtuple2
        sh
        (spec_serialize_recursive_payload sp)
      )
      sp.synth_recip
      ()
    )

let get_children
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (x: p.t)
: Tot (list p.t)
= dsnd (s.synth_recip x)

[@@erasable]
noeq
type fold_recursive_t
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (t: Type)
: Type
= {
    step: (t -> p.t -> t);
    fold: (t -> p.t -> t);
    prf: (
      (init: t) ->
      (x: p.t) ->
      Lemma
      (fold init x ==
        List.Tot.fold_left
          fold
          (step init x)
          (get_children s x) 
      )
    );
  }

let list_fold_left_append
  (#a #b: Type)
  (f: a -> b -> Tot a)
  (l1 l2: list b)
  (x: a)
: Tot (squash (List.Tot.fold_left f x (l1 `List.Tot.append` l2) == List.Tot.fold_left f (List.Tot.fold_left f x l1) l2))
= List.Tot.fold_left_append f l1 l2

let fold_recursive_cons_eq
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (#t: Type)
  (fold: fold_recursive_t s t)
  (init: t)
  (hd: p.t)
  (tl: list p.t)
  (l': list p.t)
: Lemma
  (requires (
    l' == List.Tot.append (get_children s hd) tl
  ))
  (ensures (
    List.Tot.fold_left fold.fold init (hd :: tl) == List.Tot.fold_left fold.fold (fold.step init hd) l'
  ))
= fold.prf init hd;
  list_fold_left_append fold.fold (get_children s hd) tl (fold.step init hd)

[@@erasable]
noeq
type pred_recursive_t
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
: Type
= {
    base: (p.t -> bool);
    pred: (p.t -> bool);
    prf: (
      (x: p.t) ->
      Lemma
      (pred x == (base x && List.Tot.for_all pred (get_children s x)))
    );
  }

let fold_of_pred_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (pred: pred_recursive_t s)
: Tot (fold_recursive_t s bool)
= let base = pred.base in
  let pr = pred.pred in
  {
    step = LowParse.WellFounded.forall_list_f_weak base;
    fold = LowParse.WellFounded.forall_list_f_weak pr;
    prf = (fun aux x ->
      pred.prf x;
      LowParse.WellFounded.for_all_fold_left_aux pr (aux && base x) (get_children s x)
    );
  }
