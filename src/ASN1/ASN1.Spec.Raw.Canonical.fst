module ASN1.Spec.Raw.Canonical

(* Encodable values are canonical: for every well-formed schema `k`, every
   value parsed by the typed parser `asn1_as_parser k` has the elements of
   each of its SET OF sorted by their encodings (`ASN1.Spec.Raw.canonical`),
   since the SET OF parser only accepts sorted elements.  Hence
   `ASN1.Spec.Raw.check_ser` inverts `ASN1.Spec.Raw.forget` on every
   encodable value (`check_ser_forget_encodable` below.)

   The proof follows the structure of the proof of `to_value` soundness
   (ASN1.Spec.ToValue.Sound, ASN1.Spec.ToValue.Set, ASN1.Spec.ToValue.Main),
   with a Boolean predicate on parsed values instead of their encodings. *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List
open LowParse.Tot.VLGen
open LowParse.Tot.Defaultable

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.Value
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Spec.Any
open ASN1.Spec.Set
open ASN1.Spec.Interpreter
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue
open ASN1.Spec.ToValue.Sound
open ASN1.Spec.Serializer
open ASN1.Spec.Raw

module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot
module TVM = ASN1.Spec.ToValue.Main

(* Parsers whose results satisfy a predicate *)

let psound (#k: parser_kind) (#t: Type) (p: parser k t) (q: t -> GTot bool) : prop =
  forall b. match parse p b with
  | Some (x, _) -> q x == true
  | None -> True

let psound_twin (#k: parser_kind) (#t: Type) (fp: asn1_id_t -> parser k t) (q: t -> GTot bool) : prop =
  forall id b. match parse (fp id) b with
  | Some (x, _) -> q x == true
  | None -> True

let psound_ext (#k: parser_kind) (#t: Type) (p: parser k t) (q1 q2: t -> GTot bool)
: Lemma
  (requires (psound p q1 /\ (forall x. q1 x == q2 x)))
  (ensures (psound p q2))
= ()

(* Identifier, then length-prefixed contents *)

#push-options "--z3rlimit 64"
let lc_p
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (q: asn1_content_t ack -> GTot bool)
  (b: bytes)
: Lemma
  (requires (psound p q))
  (ensures (match parse (parse_asn1_LC p) b with
    | Some (x, _) -> q x == true
    | None -> True))
= vlgen_eq p b;
  match parse parse_asn1_length_u32_t b with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then ()
    else begin
      let ct = Seq.slice b sz (sz + U32.v len) in
      match parse p ct with
      | Some (x, m) -> ()
      | None -> ()
    end

let ilc_p
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (q: asn1_content_t ack -> GTot bool)
  (b: bytes)
: Lemma
  (requires (psound p q))
  (ensures (match parse (parse_asn1_ILC id p) b with
    | Some (x, _) -> q x == true
    | None -> True))
= let pf = parse_asn1_identifier_U32 `parse_filter` (fun id' -> id' = id) in
  parse_synth_eq (pf `nondep_then` parse_asn1_LC p) snd b;
  nondep_then_eq pf (parse_asn1_LC p) b;
  parse_filter_eq parse_asn1_identifier_U32 (fun id' -> id' = id) b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id', c1) ->
    if id' = id
    then lc_p p q (Seq.slice b c1 (Seq.length b))
  | None -> ()
#pop-options

let ilc_psound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (q: asn1_content_t ack -> GTot bool)
: Lemma
  (requires (psound p q))
  (ensures (psound (parse_asn1_ILC id p) q))
= Classical.forall_intro (Classical.move_requires (ilc_p id p q))

let lc_twin_psound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (q: asn1_content_t ack -> GTot bool)
: Lemma
  (requires (psound p q))
  (ensures (psound_twin (parse_asn1_ILC_twin id p) q))
= let prf (id': asn1_id_t) (b: bytes) : Lemma (match parse (parse_asn1_ILC_twin id p id') b with
    | Some (x, _) -> q x == true
    | None -> True)
  = if id = id' then lc_p p q b
  in
  Classical.forall_intro_2 prf

(* SEQUENCE OF, SET OF *)

let top_psound (#s: _) (k: asn1_k s) : prop =
  psound (asn1_as_parser k) (canonical k) /\
  psound_twin (snd (asn1_as_parser_twin k)) (canonical k)

let rec list_p_at (#s: _) (k: asn1_k s) (b: bytes)
: Lemma
  (requires (psound (asn1_as_parser k) (canonical k)))
  (ensures (match parse (parse_list (asn1_as_parser k)) b with
    | Some (l, _) -> canonical_list k l == true
    | None -> True))
  (decreases (Seq.length b))
= let p = asn1_as_parser k in
  tot_parse_list_eq p b;
  if Seq.length b = 0
  then ()
  else match parse p b with
  | Some (_, c) ->
    if c > 0 then list_p_at k (Seq.slice b c (Seq.length b))
  | None -> ()

let rec sorted_ord (ord: bytes -> bytes -> bool) (#t: Type) (enc: t -> GTot bytes) (l: list t) : GTot bool (decreases l) =
  match l with
  | a :: b :: q -> ord (enc a) (enc b) && sorted_ord ord enc (b :: q)
  | _ -> true

let set_enc (#s: _) (k: asn1_k s) (x: asn1_t k) : GTot bytes = asn1_enc k x

let set_of_post (ord: bytes -> bytes -> bool) (#s: _) (k: asn1_k s) (l: list (asn1_t k)) : GTot bool =
  canonical_list k l && sorted_ord ord (set_enc k) l

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
let rec sorted_list_aux_p
  (ord: (bytes -> bytes -> bool))
  (#s: _) (k: asn1_k s)
  (prev: bytes) (b: bytes)
: Lemma
  (requires (psound (asn1_as_parser k) (canonical k) /\ TVM.top_esound k))
  (ensures (match tot_parse_byte_sorted_list_aux ord (asn1_as_parser k) prev b with
    | Some (l, _) -> set_of_post ord k l == true /\ (match l with a :: _ -> ord prev (set_enc k a) == true | [] -> True)
    | None -> True))
  (decreases (Seq.length b))
= let p = asn1_as_parser k in
  if Seq.length b = 0
  then ()
  else match parse p b with
  | None -> ()
  | Some (a, c) ->
    if c = 0 then ()
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      assert (Seq.slice b 0 c == set_enc k a);
      sorted_list_aux_p ord k (Seq.slice b 0 c) b';
      if ord prev (Seq.slice b 0 c)
      then match tot_parse_byte_sorted_list_aux ord p (Seq.slice b 0 c) b' with
      | None -> ()
      | Some (q, _) ->
        assert (tot_parse_byte_sorted_list_aux ord p prev b == Some (a :: q, c + snd (Some?.v (tot_parse_byte_sorted_list_aux ord p (Seq.slice b 0 c) b'))));
        assert (canonical k a == true);
        assert (set_of_post ord k (a :: q) == true)
    end

let sorted_list_p
  (ord: (bytes -> bytes -> bool))
  (#s: _) (k: asn1_k s)
  (b: bytes)
: Lemma
  (requires (psound (asn1_as_parser k) (canonical k) /\ TVM.top_esound k))
  (ensures (match tot_parse_byte_sorted_list_bare ord (asn1_as_parser k) b with
    | Some (l, _) -> set_of_post ord k l == true
    | None -> True))
= let p = asn1_as_parser k in
  if Seq.length b = 0
  then ()
  else match parse p b with
  | None -> ()
  | Some (a, c) ->
    if c = 0 then ()
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      assert (Seq.slice b 0 c == set_enc k a);
      sorted_list_aux_p ord k (Seq.slice b 0 c) b';
      match tot_parse_byte_sorted_list_aux ord p (Seq.slice b 0 c) b' with
      | None -> ()
      | Some (q, _) ->
        assert (tot_parse_byte_sorted_list_bare ord p b == Some (a :: q, c + snd (Some?.v (tot_parse_byte_sorted_list_aux ord p (Seq.slice b 0 c) b'))));
        assert (canonical k a == true);
        assert (set_of_post ord k (a :: q) == true)
    end
#pop-options

let rec sorted_ord_lex (ord: bytes -> bytes -> bool) (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma
  (requires (sorted_ord ord (set_enc k) l == true /\ (forall x y. ord x y == lex_byte_order x y)))
  (ensures (sorted_enc (asn1_enc k) l == true))
  (decreases l)
= match l with
  | _ :: b :: q -> sorted_ord_lex ord k (b :: q)
  | _ -> ()

let sized_list_p (ne: bool) (#s: _) (k: asn1_k s)
: Lemma
  (requires (psound (asn1_as_parser k) (canonical k)))
  (ensures (psound (parse_sized_list ne (asn1_as_parser k)) (canonical_list k)))
= let prf (b: bytes) : Lemma (match parse (parse_sized_list ne (asn1_as_parser k)) b with
    | Some (l, _) -> canonical_list k l == true
    | None -> True)
  = parse_filter_eq (parse_list (asn1_as_parser k)) (list_size_ok ne) b;
    list_p_at k b
  in
  Classical.forall_intro prf

let set_of_canon (#s: _) (k: asn1_k s) (l: list (asn1_t k)) : GTot bool =
  sorted_enc (asn1_enc k) l && canonical_list k l

let sized_set_p (ne: bool) (#s: _) (k: asn1_k s)
: Lemma
  (requires (psound (asn1_as_parser k) (canonical k) /\ TVM.top_esound k))
  (ensures (psound (parse_sized_set ne (asn1_as_parser k)) (set_of_canon k)))
= let p = asn1_as_parser k in
  let tord : (x: bytes -> y: bytes -> Pure bool True (fun z -> z == true <==> prop_order_of_bool_order lex_byte_order x y)) =
    fun x1 x2 -> lex_byte_order x1 x2 in
  let ord : bytes -> bytes -> bool = tord in
  let prf (b: bytes) : Lemma (match parse (parse_sized_set ne p) b with
    | Some (l, _) -> set_of_canon k l == true
    | None -> True)
  = parse_filter_eq (parse_asn1_set_of p) (list_size_ok ne) b;
    tot_parse_byte_sorted_list_correct (prop_order_of_bool_order lex_byte_order) tord p b;
    let q = tot_parse_byte_sorted_list lex_byte_order p in
    assert (parse (parse_asn1_set_of p) b == parse q b);
    assert (parse q b == q b);
    assert (q b == LowParse.Spec.Base.parse (parse_byte_sorted_list (prop_order_of_bool_order lex_byte_order) #_ #asn1_strong_parser_kind p) b);
    assert (parse (parse_asn1_set_of p) b == tot_parse_byte_sorted_list_bare ord p b);
    sorted_list_p ord k b;
    match parse (parse_asn1_set_of p) b with
    | Some (l, _) -> sorted_ord_lex ord k l
    | None -> ()
  in
  Classical.forall_intro prf

(* SEQUENCE items *)

let pure_canon (it: gen_decorated_parser_twin) (x: asn1_decorated_pure_t (Mkgendcparser?.d it)) : GTot bool =
  match it with
  | Mkgendcparser d _ _ ->
    let (| _, _, dk |) = d in
    match dk with
    | ASN1_PLAIN_ILC k -> canonical k x
    | ASN1_OPTION_ILC k -> canonical k x
    | _ -> true

let item_canon (it: gen_decorated_parser_twin) (x: asn1_decorated_t (Mkgendcparser?.d it)) : GTot bool =
  match it with
  | Mkgendcparser d _ _ ->
    let (| _, _, dk |) = d in
    canonical_dec dk x

let item_psound (it: gen_decorated_parser_twin) : prop =
  psound_twin (Mkgendcparser?.fp it) (pure_canon it)

let rec items_psound (its: list gen_decorated_parser_twin) : Tot prop (decreases its) =
  match its with
  | [] -> True
  | hd :: tl -> item_psound hd /\ items_psound tl

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let item_twin_p (it: gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (item_psound it))
  (ensures (match parse (parse_asn1_sequence_item_twin it id) b with
    | Some (x, _) -> item_canon it x == true
    | None -> True))
= match it with
  | Mkgendcparser d p fp ->
    let (| _, _, dk |) = d in
    assert (match parse (fp id) b with
      | Some (x, _) -> pure_canon it x == true
      | None -> True);
    match dk with
    | ASN1_PLAIN_ILC _ -> ()
    | ASN1_OPTION_ILC _ -> parse_synth_eq (fp id) Some b
    | ASN1_DEFAULT_TERMINAL _ #k_dl defv_l -> ()
    | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k_dl r defv_l -> ()
#pop-options

let rec seq_canon (its: list gen_decorated_parser_twin) (x: asn1_sequence_t (List.map Mkgendcparser?.d its)) : GTot bool (decreases its) =
  match its with
  | [] -> true
  | [hd] -> item_canon hd x
  | hd :: tl ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & asn1_sequence_t (List.map Mkgendcparser?.d tl) = x in
    item_canon hd (fst x') && seq_canon tl (snd x')

let item_default_canon (it: gen_decorated_parser_twin)
: Lemma (match generate_defaultable_item it with
    | Some v -> item_canon it v == true
    | None -> True)
= ()

let rec seq_default_canon (its: list gen_decorated_parser_twin)
: Lemma
  (ensures (match generate_defaultable_items its with
    | Some v -> seq_canon its v == true
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | [hd] -> item_default_canon hd
  | hd :: tl -> item_default_canon hd; seq_default_canon tl

(* The SEQUENCE machine *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec seq_pmachine (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (items_psound its))
  (ensures (match parse (make_asn1_sequence_parser' its st) b with
    | Some (x, _) -> seq_canon its x == true
    | None -> True))
  (decreases %[its; 2])
= match its with
  | [] -> ()
  | _ ->
    seq'_veq its st b;
    seq_default_canon its;
    seq_pbody its st b

and seq_pbody (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_psound its))
  (ensures (match parse (make_asn1_sequence_parser'' its st) b with
    | Some (x, _) -> seq_canon its x == true
    | None -> True))
  (decreases %[its; 1])
= seq''_veq its st b;
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  match st with
  | None ->
    and_then_eq (weaken k parse_asn1_identifier_U32) pbt b;
    begin match parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) ->
      seq_ptwin its id (Seq.slice b c1 (Seq.length b))
    end
  | Some id ->
    and_then_eq (weaken k (parse_ret id)) pbt b;
    Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
    seq_ptwin its id b

and seq_ptwin (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_psound its))
  (ensures (match parse (make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' id) b with
    | Some (x, _) -> seq_canon its x == true
    | None -> True))
  (decreases %[its; 0])
= match its with
  | [hd] ->
    body_twin_veq_single hd id b;
    item_twin_p hd id b
  | hd :: hd' :: tl ->
    body_twin_veq_cons hd hd' tl id b;
    let Mkgendcparser d _ _ = hd in
    let (| s, de, dk |) = d in
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) None in
      nondep_then_eq p1 p2 b;
      item_twin_p hd id b;
      match parse p1 b with
      | None -> ()
      | Some (x1, c) ->
        seq_pmachine (hd' :: tl) None (Seq.slice b c (Seq.length b))
    end
    else match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      item_default_canon hd;
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) (Some id) in
      nondep_then_eq p1 p2 b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      seq_pmachine (hd' :: tl) (Some id) b
#pop-options

let seq_parser_psound (its: list gen_decorated_parser_twin)
: Lemma
  (requires (items_psound its))
  (ensures (psound (make_asn1_sequence_parser its) (seq_canon its)))
= Classical.forall_intro (Classical.move_requires (seq_pmachine its None))

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec items_seq_canon (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items)
: Lemma
  (ensures (
    asn1_sequence_t_core_equiv items;
    canonical_items items x == seq_canon (asn1_sequence_as_parser items) x))
  (decreases items)
= asn1_sequence_t_core_equiv items;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    items_seq_canon tl (snd x')
#pop-options

(* The ANY DEFINED BY machine *)

let rec any_canon (its: list gen_decorated_parser_twin) (#t: Type) (sq: t -> GTot bool) (x: asn1_sequence_any_t (List.map Mkgendcparser?.d its) t) : GTot bool (decreases its) =
  match its with
  | [] -> sq x
  | [hd] ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & t = x in
    item_canon hd (fst x') && sq (snd x')
  | hd :: tl ->
    let x' : asn1_decorated_t (Mkgendcparser?.d hd) & asn1_sequence_any_t (List.map Mkgendcparser?.d tl) t = x in
    item_canon hd (fst x') && any_canon tl sq (snd x')

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec items_any_canon (#ids: _) (items: asn1_gen_items_l ids) (#t: Type) (sq: t -> GTot bool) (x: asn1_sequence_any_t_core items t)
: Lemma
  (ensures (
    asn1_sequence_any_t_equiv items t;
    (canonical_items_any items x && sq (items_any_sfx items x)) == any_canon (asn1_sequence_as_parser items) sq x))
  (decreases items)
= asn1_sequence_any_t_equiv items t;
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl t = x in
    items_any_canon tl sq (snd x')
#pop-options

let sfx_psound (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sq: t -> GTot bool) : prop =
  psound (Mkparsertwin?.p sfx) sq /\
  psound_twin (Mkparsertwin?.fp sfx) sq

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let rec any_pmachine (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sq: t -> GTot bool) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (items_psound its /\ sfx_psound sfx sq))
  (ensures (match parse (make_asn1_sequence_any_parser' its sfx st) b with
    | Some (x, _) -> any_canon its sq x == true
    | None -> True))
  (decreases %[its; 1])
= match its with
  | [] -> any'_veq_nil sfx st b
  | _ ->
    any'_veq_cons its sfx st b;
    let pb = make_asn1_sequence_any_parser'' its sfx in
    match st with
    | None ->
      and_then_eq (any_guard_p None) pb b;
      begin match parse parse_asn1_identifier_U32 b with
      | None -> ()
      | Some (id, c1) ->
        any_ptwin its sfx sq id (Seq.slice b c1 (Seq.length b))
      end
    | Some id ->
      and_then_eq (any_guard_p st) pb b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      any_ptwin its sfx sq id b

and any_ptwin (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sq: t -> GTot bool) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_psound its /\ sfx_psound sfx sq))
  (ensures (match parse (make_asn1_sequence_any_parser'' its sfx id) b with
    | Some (x, _) -> any_canon its sq x == true
    | None -> True))
  (decreases %[its; 0])
= let hd :: tl = its in
  any''_veq hd tl sfx id b;
  let Mkgendcparser d _ _ = hd in
  let (| s, de, dk |) = d in
  match tl with
  | [] ->
    any_body_veq_single hd sfx id b;
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_any_parser' [] sfx None in
      nondep_then_eq p1 p2 b;
      item_twin_p hd id b;
      match parse p1 b with
      | None -> ()
      | Some (x1, c) ->
        any_pmachine [] sfx sq None (Seq.slice b c (Seq.length b))
    end
    else begin match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      item_default_canon hd;
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_any_parser' [] sfx (Some id) in
      nondep_then_eq p1 p2 b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      any_pmachine [] sfx sq (Some id) b
    end
  | hd' :: tl' ->
    any_body_veq_cons hd hd' tl' sfx id b;
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_any_parser' tl sfx None in
      nondep_then_eq p1 p2 b;
      item_twin_p hd id b;
      match parse p1 b with
      | None -> ()
      | Some (x1, c) ->
        any_pmachine tl sfx sq None (Seq.slice b c (Seq.length b))
    end
    else begin match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      item_default_canon hd;
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_any_parser' tl sfx (Some id) in
      nondep_then_eq p1 p2 b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      any_pmachine tl sfx sq (Some id) b
    end
#pop-options

let any_parser_psound (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (sq: t -> GTot bool)
: Lemma
  (requires (items_psound its /\ sfx_psound sfx sq))
  (ensures (psound (make_asn1_sequence_any_parser its sfx) (any_canon its sq)))
= Classical.forall_intro (Classical.move_requires (any_pmachine its sfx sq None))

(* CHOICE *)

let content_psound (k: asn1_content_k) : prop =
  psound (asn1_content_as_parser k) (canonical_content k)

let rec lc_psound (lc: list (asn1_id_t & asn1_content_k)) : Tot prop (decreases lc) =
  match lc with
  | [] -> True
  | (_, y) :: tl -> content_psound y /\ lc_psound tl

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let choice_payload_step_p
  (x: asn1_id_t) (y: asn1_content_k)
  (tl: list (asn1_id_t & asn1_content_k))
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (requires (id <> x))
  (ensures (
    match parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser ((x, y) :: tl)) id) b, parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser tl) id) b with
    | Some (v, _), Some (v', _) -> canonical_choice ((x, y) :: tl) (dfst v) (dsnd v) == canonical_choice tl (dfst v') (dsnd v')
    | None, None -> True
    | _ -> False))
= let hdp = (x, Mkgenparser (asn1_content_t y) (parse_asn1_LC (asn1_content_as_parser y))) in
  assert (asn1_lc_as_parser ((x, y) :: tl) == hdp :: asn1_lc_as_parser tl) by (FStar.Tactics.norm [delta_only [`%asn1_lc_as_parser; `%dasn1_lc_as_parser]; zeta; iota]; FStar.Tactics.smt ());
  choice_payload_unfold hdp (asn1_lc_as_parser tl) id b;
  match parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser tl) id) b with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_lc_as_parser tl)) id (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()

let rec choice_payload_p
  (lc: list (asn1_id_t & asn1_content_k))
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (requires (lc_psound lc))
  (ensures (match parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) b with
    | Some (v, _) -> canonical_choice lc (dfst v) (dsnd v) == true
    | None -> True))
  (decreases lc)
= let lp = asn1_lc_as_parser lc in
  match lc with
  | [] -> ()
  | (x, y) :: tl ->
    if id = x
    then begin
      let p = parse_asn1_LC (asn1_content_as_parser y) in
      parse_synth_eq p (attach_tag lp id) b;
      assert (content_psound y);
      lc_p (asn1_content_as_parser y) (canonical_content y) b;
      match parse p b with
      | Some (c, _) ->
        assert (canonical_content y c == true);
        assert (canonical_choice lc id c == canonical_content y c)
      | None -> ()
    end
    else begin
      choice_payload_p tl id b;
      choice_payload_step_p x y tl id b
    end

let choice_p_at (lc: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma
  (requires (lc_psound lc))
  (ensures (match parse (make_gen_choice_strong_parser parse_asn1_identifier_U32 (asn1_lc_as_parser lc)) b with
    | Some (v, _) -> canonical_choice lc (dfst v) (dsnd v) == true
    | None -> True))
= let lp = asn1_lc_as_parser lc in
  parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) -> choice_payload_p lc id (Seq.slice b c1 (Seq.length b))

let choice_twin_p (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (lc_psound lc))
  (ensures (match parse (parse_tagged_union_payload (project_tags (asn1_lc_as_parser lc)) (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc)) id) b with
    | Some (v, _) -> canonical_choice lc (dfst v) (dsnd v) == true
    | None -> True))
= let lp = asn1_lc_as_parser lc in
  parse_synth_eq (make_gen_choice_strong_payload_parser lp id) (synth_tagged_union_data (project_tags lp) id) b;
  choice_payload_p lc id b

let canonical_choice_eq (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.noRepeats (List.map fst lc))) (x: asn1_t (ASN1_CHOICE_ILC lc pf))
: Lemma (let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    canonical (ASN1_CHOICE_ILC lc pf) x == canonical_choice lc (dfst x') (dsnd x'))
= ()

let choice_top_psound (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.noRepeats (List.map fst lc)))
: Lemma
  (requires (lc_psound lc))
  (ensures (top_psound (ASN1_CHOICE_ILC lc pf)))
= let k = ASN1_CHOICE_ILC lc pf in
  let lp = asn1_lc_as_parser lc in
  let prf1 (b: bytes) : Lemma (match parse (asn1_as_parser k) b with
    | Some (x, _) -> canonical k x == true
    | None -> True)
  = assert (asn1_as_parser k == make_asn1_choice_parser lc pf k lp);
    choice_p_at lc b;
    match parse (make_gen_choice_strong_parser parse_asn1_identifier_U32 lp) b with
    | Some (v, _) -> canonical_choice_eq lc pf v
    | None -> ()
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (snd (asn1_as_parser_twin k) id) b with
    | Some (x, _) -> canonical k x == true
    | None -> True)
  = assert (snd (asn1_as_parser_twin k) id == make_asn1_choice_parser_twin_cases lc pf k lp id);
    choice_twin_p lc id b;
    match parse (parse_tagged_union_payload (project_tags lp) (make_gen_choice_strong_payload_parser lp) id) b with
    | Some (v, _) -> canonical_choice_eq lc pf v
    | None -> ()
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2;
  assert (psound (asn1_as_parser k) (canonical k));
  assert (psound_twin (snd (asn1_as_parser_twin k)) (canonical k))
#pop-options

(* ANY DEFINED BY: the supported payloads *)

let rec ls_psound (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot prop (decreases ls) =
  match ls with
  | [] -> True
  | (_, y) :: tl -> items_psound (asn1_sequence_as_parser (dsnd y)) /\ ls_psound tl

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let ls_payload_step_p (key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (b: bytes)
: Lemma
  (requires (key <> key_of_lit key_k x))
  (ensures (
    match parse (make_gen_choice_weak_payload_parser (adb_lp key_k ((x, y) :: tl)) key) b, parse (make_gen_choice_weak_payload_parser (adb_lp key_k tl) key) b with
    | Some (v, _), Some (v', _) -> canonical_ls key_k ((x, y) :: tl) (dfst v) (dsnd v) == canonical_ls key_k tl (dfst v') (dsnd v')
    | None, None -> True
    | _ -> False))
= let t = asn1_terminal_t key_k in
  let f = key_of_lit key_k in
  let hdp = ls_hd (f x) y in
  ls_as_parser_cons t f x y tl;
  weak_payload_unfold hdp (asn1_ls_as_parser t f tl) key b;
  match parse (make_gen_choice_weak_payload_parser (asn1_ls_as_parser t f tl) key) b with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_ls_as_parser t f tl)) key (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()

let rec ls_payload_p (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (b: bytes)
: Lemma
  (requires (ls_psound ls))
  (ensures (match parse (make_gen_choice_weak_payload_parser (adb_lp key_k ls) key) b with
    | Some (v, _) -> canonical_ls key_k ls (dfst v) (dsnd v) == true
    | None -> True))
  (decreases ls)
= let t = asn1_terminal_t key_k in
  let f = key_of_lit key_k in
  let lp = asn1_ls_as_parser t f ls in
  match ls with
  | [] -> ()
  | (x, y) :: tl ->
    if key = f x
    then begin
      let items = dsnd y in
      let p = make_asn1_sequence_parser (asn1_sequence_as_parser items) in
      ls_as_parser_cons t f x y tl;
      parse_synth_eq p (attach_tag lp key) b;
      seq_parser_psound (asn1_sequence_as_parser items);
      match parse p b with
      | Some (c, _) -> items_seq_canon items c
      | None -> ()
    end
    else begin
      ls_payload_p key_k tl key b;
      ls_payload_step_p key_k x y tl key b
    end

let ls_fb_payload_step_p (k0: asn1_content_k) (key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (key: asn1_terminal_t key_k) (b: bytes)
: Lemma
  (requires (key <> key_of_lit key_k x /\ ((x, y) :: tl) << k0 /\ dsnd fb << k0))
  (ensures (
    match parse (make_gen_choice_with_fallback_weak_payload_parser (adb_lp key_k ((x, y) :: tl)) (fb_gp fb) key) b, parse (make_gen_choice_with_fallback_weak_payload_parser (adb_lp key_k tl) (fb_gp fb) key) b with
    | Some (v, _), Some (v', _) -> canonical_ls_fb k0 key_k ((x, y) :: tl) (dsnd fb) (dfst v) (dsnd v) == canonical_ls_fb k0 key_k tl (dsnd fb) (dfst v') (dsnd v')
    | None, None -> True
    | _ -> False))
= let t = asn1_terminal_t key_k in
  let f = key_of_lit key_k in
  let hdp = ls_hd (f x) y in
  ls_as_parser_cons t f x y tl;
  weak_payload_fb_unfold hdp (asn1_ls_as_parser t f tl) (fb_gp fb) key b;
  match parse (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser t f tl) (fb_gp fb) key) b with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_with_fallback_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_ls_as_parser t f tl)) (Mkgenparser?.t (fb_gp fb)) key (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_with_fallback_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()

let rec ls_fb_payload_p (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (key: asn1_terminal_t key_k) (b: bytes)
: Lemma
  (requires (ls_psound ls /\ items_psound (asn1_sequence_as_parser (dsnd fb)) /\ ls << k0 /\ dsnd fb << k0))
  (ensures (match parse (make_gen_choice_with_fallback_weak_payload_parser (adb_lp key_k ls) (fb_gp fb) key) b with
    | Some (v, _) -> canonical_ls_fb k0 key_k ls (dsnd fb) (dfst v) (dsnd v) == true
    | None -> True))
  (decreases ls)
= let t = asn1_terminal_t key_k in
  let f = key_of_lit key_k in
  let lp = asn1_ls_as_parser t f ls in
  match ls with
  | [] ->
    let p = make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd fb)) in
    parse_synth_eq p (attach_tag_with_fallback lp (fb_gp fb) key) b;
    seq_parser_psound (asn1_sequence_as_parser (dsnd fb));
    begin match parse p b with
    | Some (c, _) -> items_seq_canon (dsnd fb) c
    | None -> ()
    end
  | (x, y) :: tl ->
    if key = f x
    then begin
      let items = dsnd y in
      let p = make_asn1_sequence_parser (asn1_sequence_as_parser items) in
      ls_as_parser_cons t f x y tl;
      parse_synth_eq p (attach_tag_with_fallback lp (fb_gp fb) key) b;
      seq_parser_psound (asn1_sequence_as_parser items);
      match parse p b with
      | Some (c, _) -> items_seq_canon items c
      | None -> ()
    end
    else begin
      ls_fb_payload_p k0 key_k tl fb key b;
      ls_fb_payload_step_p k0 key_k x y tl fb key b
    end
#pop-options

(* ANY DEFINED BY: the suffix (key, then payload) *)

let adb_sq (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (s: make_gen_choice_type (extract_types (adb_lp key_k ls)))
: GTot bool
= canonical_ls key_k ls (dfst s) (dsnd s)

let adb_fb_sq (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (fb: asn1_gen_items_lk { dsnd fb << k0 })
  (s: make_gen_choice_type_with_fallback (extract_types (adb_lp key_k ls)) (Mkgenparser?.t (fb_gp fb)))
: GTot bool
= canonical_ls_fb k0 key_k ls (dsnd fb) (dfst s) (dsnd s)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let adb_sfx_psound (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Lemma
  (requires (ls_psound ls))
  (ensures (sfx_psound (adb_sfx kid key_k ls) (adb_sq key_k ls)))
= let lp = adb_lp key_k ls in
  let prf1 (b: bytes) : Lemma (match parse (Mkparsertwin?.p (adb_sfx kid key_k ls)) b with
    | Some (x, _) -> adb_sq key_k ls x == true
    | None -> True)
  = parse_tagged_union_eq (adb_key_p kid key_k) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) b;
    match parse (adb_key_p kid key_k) b with
    | None -> ()
    | Some (key, c1) -> ls_payload_p key_k ls key (Seq.slice b c1 (Seq.length b))
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (Mkparsertwin?.fp (adb_sfx kid key_k ls) id) b with
    | Some (x, _) -> adb_sq key_k ls x == true
    | None -> True)
  = assert (parse (Mkparsertwin?.fp (adb_sfx kid key_k ls) id) b == parse (weaken asn1_weak_parser_kind (parse_tagged_union (adb_key_fp kid key_k id) (tag_of_gen_choice_type (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls))) (make_gen_choice_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)))) b)
      by (FStar.Tactics.norm [delta_only [`%adb_sfx; `%Mkparsertwin?.fp; `%make_gen_choice_weak_parser_twin; `%adb_lp]; zeta; iota]; FStar.Tactics.trefl ());
    parse_tagged_union_eq (adb_key_fp kid key_k id) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) b;
    match parse (adb_key_fp kid key_k id) b with
    | None -> ()
    | Some (key, c1) -> ls_payload_p key_k ls key (Seq.slice b c1 (Seq.length b))
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

let adb_fb_sfx_psound (k0: asn1_content_k) (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (fb: asn1_gen_items_lk { dsnd fb << k0 })
: Lemma
  (requires (ls_psound ls /\ items_psound (asn1_sequence_as_parser (dsnd fb))))
  (ensures (sfx_psound (adb_fb_sfx kid key_k ls fb) (adb_fb_sq k0 key_k ls fb)))
= let lp = adb_lp key_k ls in
  let prf1 (b: bytes) : Lemma (match parse (Mkparsertwin?.p (adb_fb_sfx kid key_k ls fb)) b with
    | Some (x, _) -> adb_fb_sq k0 key_k ls fb x == true
    | None -> True)
  = parse_tagged_union_eq (adb_key_p kid key_k) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (fb_gp fb)) b;
    match parse (adb_key_p kid key_k) b with
    | None -> ()
    | Some (key, c1) -> ls_fb_payload_p k0 key_k ls fb key (Seq.slice b c1 (Seq.length b))
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (Mkparsertwin?.fp (adb_fb_sfx kid key_k ls fb) id) b with
    | Some (x, _) -> adb_fb_sq k0 key_k ls fb x == true
    | None -> True)
  = assert (parse (Mkparsertwin?.fp (adb_fb_sfx kid key_k ls fb) id) b == parse (weaken asn1_weak_parser_kind (parse_tagged_union (adb_key_fp kid key_k id) (tag_of_gen_choice_type_with_fallback (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (fb_gp fb)))) b)
      by (FStar.Tactics.norm [delta_only [`%adb_fb_sfx; `%Mkparsertwin?.fp; `%make_gen_choice_with_fallback_weak_parser_twin; `%adb_lp]; zeta; iota]; FStar.Tactics.trefl ());
    parse_tagged_union_eq (adb_key_fp kid key_k id) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (fb_gp fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (fb_gp fb)) b;
    match parse (adb_key_fp kid key_k id) b with
    | None -> ()
    | Some (key, c1) -> ls_fb_payload_p k0 key_k ls fb key (Seq.slice b c1 (Seq.length b))
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2
#pop-options

(* ANY DEFINED BY contents *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let adb_content_psound
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma
  (requires (items_psound (asn1_sequence_as_parser prefix) /\ ls_psound ls))
  (ensures (content_psound (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf')))
= let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf' in
  adb_sfx_psound kid key_k ls;
  any_parser_psound (asn1_sequence_as_parser prefix) (adb_sfx kid key_k ls) (adb_sq key_k ls);
  assert (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') == make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_sfx kid key_k ls))
    by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser; `%adb_sfx; `%adb_lp; `%adb_key_p; `%adb_key_fp]; zeta; iota]; FStar.Tactics.trefl ());
  let prf (x: asn1_content_t k) : Lemma (canonical_content k x == any_canon (asn1_sequence_as_parser prefix) (adb_sq key_k ls) x) =
    items_any_canon prefix (adb_sq key_k ls) x
  in
  Classical.forall_intro prf

let adb_fb_content_psound
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma
  (requires (items_psound (asn1_sequence_as_parser prefix) /\ ls_psound ls /\ items_psound (asn1_sequence_as_parser fbitems)))
  (ensures (content_psound (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf')))
= let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf' in
  let fb : asn1_gen_items_lk = (| fbids, fbitems |) in
  fb_precedes k;
  adb_fb_sfx_psound k kid key_k ls fb;
  any_parser_psound (asn1_sequence_as_parser prefix) (adb_fb_sfx kid key_k ls fb) (adb_fb_sq k key_k ls fb);
  assert (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') == make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_fb_sfx kid key_k ls (| fbids, fbitems |)))
    by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser; `%adb_fb_sfx; `%adb_lp; `%adb_key_p; `%adb_key_fp; `%fb_gp]; zeta; iota]; FStar.Tactics.trefl ());
  let prf (x: asn1_content_t k) : Lemma (canonical_content k x == any_canon (asn1_sequence_as_parser prefix) (adb_fb_sq k key_k ls fb) x) =
    items_any_canon prefix (adb_fb_sq k key_k ls fb) x
  in
  Classical.forall_intro prf
#pop-options

(* SET *)

let rec elem_canon (its: list gen_decorated_parser_twin) (e: set_elem_t its) : GTot bool (decreases its) =
  match its with
  | [] -> false
  | hd :: tl ->
    let e' : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
    match e' with
    | Inl v -> item_canon hd v
    | Inr e'' -> elem_canon tl e''

let rec elems_canon (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) : GTot bool (decreases l) =
  match l with
  | [] -> true
  | e :: q -> elem_canon its e && elems_canon its q

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec set_elem_twin_p (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (items_psound its))
  (ensures (match parse (parse_set_elem_twin its id) b with
    | Some (e, _) -> elem_canon its e == true
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    if FStar.Set.mem id s
    then begin
      item_twin_p hd id b;
      parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b
    end
    else begin
      set_elem_twin_p tl id b;
      parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b
    end
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_elem_p (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_psound its))
  (ensures (match parse (parse_set_elem its) b with
    | Some (e, _) -> elem_canon its e == true
    | None -> True))
= parse_set_elem_twin_cases_injective its;
  and_then_eq parse_asn1_identifier_U32 (parse_set_elem_twin its) b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id, c1) ->
    set_elem_twin_p its id (Seq.slice b c1 (Seq.length b))
  | None -> ()

let rec set_list_p (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_psound its))
  (ensures (match parse (parse_list (parse_set_elem its)) b with
    | Some (l, _) -> elems_canon its l == true
    | None -> True))
  (decreases (Seq.length b))
= let p = parse_set_elem its in
  tot_parse_list_eq p b;
  if Seq.length b = 0
  then ()
  else match parse p b with
  | Some (e, c) ->
    set_elem_p its b;
    if c > 0 then begin
      let b' = Seq.slice b c (Seq.length b) in
      set_list_p its b';
      match parse (parse_list p) b' with
      | Some (l', _) -> assert (elems_canon its (e :: l') == (elem_canon its e && elems_canon its l'))
      | None -> ()
    end
  | None -> ()
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec heads_tails_canon (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (l: list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)))
: Lemma
  (requires (elems_canon (hd :: tl) l == true))
  (ensures (
    (forall v. List.memP v (heads l) ==> item_canon hd v == true) /\
    elems_canon tl (tails l) == true))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> heads_tails_canon hd tl q

let comp_canon (hd: gen_decorated_parser_twin) (h: list (asn1_decorated_t (Mkgendcparser?.d hd)) { comp_ok hd h })
: Lemma
  (requires (forall v. List.memP v h ==> item_canon hd v == true))
  (ensures (item_canon hd (comp_value hd h) == true))
= match h with
  | [v] -> ()
  | [] -> item_default_canon hd

let rec set_tuple_canon (its: list gen_decorated_parser_twin) (l: list (set_elem_t its) { comps_ok its l })
: Lemma
  (requires (elems_canon its l == true))
  (ensures (seq_canon its (set_to_tuple' its l) == true))
  (decreases its)
= match its with
  | [] -> ()
  | [hd] ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t [])) = l in
    heads_tails_canon hd [] l';
    comp_canon hd (heads l')
  | hd :: tl ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
    heads_tails_canon hd tl l';
    comp_canon hd (heads l');
    set_tuple_canon tl (tails l')
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_parser_psound (its: list gen_decorated_parser_twin)
: Lemma
  (requires (items_psound its))
  (ensures (psound (make_asn1_set_parser its) (seq_canon its)))
= set_to_tuple_injective its;
  let pl = parse_list (parse_set_elem its) in
  let prf (b: bytes) : Lemma (match parse (make_asn1_set_parser its) b with
    | Some (x, _) -> seq_canon its x == true
    | None -> True)
  = parse_synth_eq (pl `parse_filter` set_ok its) (set_to_tuple its) b;
    parse_filter_eq pl (set_ok its) b;
    set_list_p its b;
    match parse pl b with
    | Some (l, _) -> if set_ok its l then set_tuple_canon its l
    | None -> ()
  in
  Classical.forall_intro prf
#pop-options

(* Per-case lemmas *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let terminal_content_psound (k': asn1_terminal_k)
: Lemma (content_psound (ASN1_TERMINAL k'))
= let k = ASN1_TERMINAL k' in
  let prf (b: bytes) : Lemma (match parse (asn1_content_as_parser k) b with
    | Some (x, _) -> canonical_content k x == true
    | None -> True)
  = match parse (asn1_content_as_parser k) b with
    | Some (x, _) -> assert (canonical_content k x == true)
    | None -> ()
  in
  Classical.forall_intro prf

let restricted_content_psound (k': asn1_terminal_k) (r: asn1_restriction k')
: Lemma (content_psound (ASN1_RESTRICTED_TERMINAL k' r))
= let k = ASN1_RESTRICTED_TERMINAL k' r in
  let prf (b: bytes) : Lemma (match parse (asn1_content_as_parser k) b with
    | Some (x, _) -> canonical_content k x == true
    | None -> True)
  = match parse (asn1_content_as_parser k) b with
    | Some (x, _) -> assert (canonical_content k x == true)
    | None -> ()
  in
  Classical.forall_intro prf

let sequence_content_psound (ids: id_decs {asn1_sequence_k_wf ids}) (items: asn1_gen_items_l ids)
: Lemma
  (requires (items_psound (asn1_sequence_as_parser items)))
  (ensures (content_psound (ASN1_SEQUENCE (| ids, items |))))
= let k = ASN1_SEQUENCE (| ids, items |) in
  seq_parser_psound (asn1_sequence_as_parser items);
  Classical.forall_intro (items_seq_canon items);
  psound_ext (asn1_content_as_parser k) (seq_canon (asn1_sequence_as_parser items)) (canonical_content k)

let set_content_psound (ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids))
: Lemma
  (requires (items_psound (asn1_sequence_as_parser items)))
  (ensures (content_psound (ASN1_SET ids items pf)))
= let k = ASN1_SET ids items pf in
  set_parser_psound (asn1_sequence_as_parser items);
  Classical.forall_intro (items_seq_canon items);
  psound_ext (asn1_content_as_parser k) (seq_canon (asn1_sequence_as_parser items)) (canonical_content k)

let sequence_of_content_psound (ne: bool) (#s: _) (k': asn1_k s)
: Lemma
  (requires (top_psound k'))
  (ensures (content_psound (ASN1_SEQUENCE_OF ne k')))
= let k = ASN1_SEQUENCE_OF ne k' in
  sized_list_p ne k';
  assert (asn1_content_as_parser k == parse_sized_list ne (asn1_as_parser k'));
  let prf (x: asn1_content_t k) : Lemma (canonical_list k' x == canonical_content k x) = () in
  Classical.forall_intro prf;
  psound_ext (asn1_content_as_parser k) (canonical_list k') (canonical_content k)

let set_of_content_psound (ne: bool) (#s: _) (k': asn1_k s)
: Lemma
  (requires (top_psound k' /\ TVM.top_esound k'))
  (ensures (content_psound (ASN1_SET_OF ne k')))
= let k = ASN1_SET_OF ne k' in
  sized_set_p ne k';
  assert (asn1_content_as_parser k == parse_sized_set ne (asn1_as_parser k'));
  let prf (x: asn1_content_t k) : Lemma (set_of_canon k' x == canonical_content k x) = () in
  Classical.forall_intro prf;
  psound_ext (asn1_content_as_parser k) (set_of_canon k') (canonical_content k)

let prefixed_content_psound (#s: _) (k': asn1_k s)
: Lemma
  (requires (top_psound k'))
  (ensures (content_psound (ASN1_PREFIXED k')))
= let k = ASN1_PREFIXED k' in
  let prf (b: bytes) : Lemma (match parse (asn1_content_as_parser k) b with
    | Some (x, _) -> canonical_content k x == true
    | None -> True)
  = assert (parse (asn1_content_as_parser k) b == parse (asn1_as_parser k') b);
    match parse (asn1_as_parser k') b with
    | Some (x, _) ->
      assert (canonical k' x == true);
      assert (canonical_content k x == canonical k' x)
    | None -> ()
  in
  Classical.forall_intro prf

let ilc_top_psound (id: asn1_id_t) (k': asn1_content_k)
: Lemma
  (requires (content_psound k'))
  (ensures (top_psound (ASN1_ILC id k')))
= let k = ASN1_ILC id k' in
  let p = asn1_content_as_parser k' in
  ilc_psound id p (canonical_content k');
  lc_twin_psound id p (canonical_content k');
  assert (asn1_as_parser k == parse_asn1_ILC id p);
  assert (snd (asn1_as_parser_twin k) == parse_asn1_ILC_twin id p);
  let eq (x: asn1_t k) : Lemma (canonical k x == canonical_content k' x) = () in
  Classical.forall_intro eq;
  let prf1 (b: bytes) : Lemma (match parse (asn1_as_parser k) b with
    | Some (x, _) -> canonical k x == true
    | None -> True)
  = assert (parse (asn1_as_parser k) b == parse (parse_asn1_ILC id p) b);
    match parse (parse_asn1_ILC id p) b with
    | Some (x, _) -> assert (canonical_content k' x == true); eq x
    | None -> ()
  in
  let prf2 (id': asn1_id_t) (b: bytes) : Lemma (match parse (snd (asn1_as_parser_twin k) id') b with
    | Some (x, _) -> canonical k x == true
    | None -> True)
  = assert (parse (snd (asn1_as_parser_twin k) id') b == parse (parse_asn1_ILC_twin id p id') b);
    match parse (parse_asn1_ILC_twin id p id') b with
    | Some (x, _) -> assert (canonical_content k' x == true); eq x
    | None -> ()
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

let any_top_psound ()
: Lemma (top_psound ASN1_ANY_ILC)
= let prf1 (b: bytes) : Lemma (match parse (asn1_as_parser ASN1_ANY_ILC) b with
    | Some (x, _) -> canonical ASN1_ANY_ILC x == true
    | None -> True)
  = match parse (asn1_as_parser ASN1_ANY_ILC) b with
    | Some (x, _) -> assert (canonical ASN1_ANY_ILC x == true)
    | None -> ()
  in
  let prf2 (id: asn1_id_t) (b: bytes) : Lemma (match parse (snd (asn1_as_parser_twin ASN1_ANY_ILC) id) b with
    | Some (x, _) -> canonical ASN1_ANY_ILC x == true
    | None -> True)
  = match parse (snd (asn1_as_parser_twin ASN1_ANY_ILC) id) b with
    | Some (x, _) -> assert (canonical ASN1_ANY_ILC x == true)
    | None -> ()
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2;
  assert (psound (asn1_as_parser ASN1_ANY_ILC) (canonical ASN1_ANY_ILC));
  assert (psound_twin (snd (asn1_as_parser_twin ASN1_ANY_ILC)) (canonical ASN1_ANY_ILC))

let plain_psound (#s: _) (k: asn1_k s)
: Lemma
  (requires (top_psound k))
  (ensures (item_psound (asn1_decorated_as_parser_twin (ASN1_PLAIN_ILC k))))
= ()

let option_psound (#s: _) (k: asn1_k s)
: Lemma
  (requires (top_psound k))
  (ensures (item_psound (asn1_decorated_as_parser_twin (ASN1_OPTION_ILC k))))
= ()
#pop-options

(* The main lemma *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec content_lemma (id: asn1_id_t) (k: asn1_content_k)
: Lemma
  (requires (wf_content id k))
  (ensures (content_psound k))
  (decreases k)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' r -> restricted_content_psound k' r
  | ASN1_TERMINAL k' -> terminal_content_psound k'
  | ASN1_SEQUENCE gitems ->
    let (| ids, items |) = gitems in
    items_lemma items;
    sequence_content_psound ids items
  | ASN1_SET ids items pf ->
    items_lemma items;
    set_content_psound ids items pf
  | ASN1_SEQUENCE_OF ne k' ->
    top_lemma k';
    sequence_of_content_psound ne k'
  | ASN1_SET_OF ne k' ->
    top_lemma k';
    TVM.top_lemma k';
    set_of_content_psound ne k'
  | ASN1_PREFIXED k' ->
    top_lemma k';
    prefixed_content_psound k'
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    items_lemma prefix;
    ls_lemma (asn1_key_lit key_k) ls;
    begin match ofb with
    | None -> adb_content_psound idp prefix kid key_k ls pf pf'
    | Some fb ->
      let (| fbids, fbitems |) = fb in
      items_lemma fbitems;
      adb_fb_content_psound idp prefix kid key_k ls fbids fbitems pf pf'
    end

and ls_lemma (t: eqtype) (ls: list (t & asn1_gen_items_lk))
: Lemma
  (requires (wf_ls ls))
  (ensures (ls_psound ls))
  (decreases ls)
= match ls with
  | [] -> ()
  | h :: tl ->
    let (_, y) = h in
    items_lemma (dsnd y);
    ls_lemma t tl

and lc_lemma (lc: list (asn1_id_t & asn1_content_k))
: Lemma
  (requires (wf_lc lc))
  (ensures (lc_psound lc))
  (decreases lc)
= match lc with
  | [] -> ()
  | h :: tl ->
    let (x, y) = h in
    content_lemma x y;
    lc_lemma tl

and top_lemma (#s: _) (k: asn1_k s)
: Lemma
  (requires (wf k))
  (ensures (top_psound k))
  (decreases k)
= match k with
  | ASN1_ILC id k' ->
    content_lemma id k';
    ilc_top_psound id k'
  | ASN1_CHOICE_ILC lc pf ->
    lc_lemma lc;
    choice_top_psound lc pf
  | ASN1_ANY_ILC -> any_top_psound ()

and dec_lemma (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma
  (requires (wf_dec dk))
  (ensures (item_psound (asn1_decorated_as_parser_twin dk)))
  (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k -> top_lemma k; plain_psound k
  | ASN1_OPTION_ILC k -> top_lemma k; option_psound k
  | ASN1_DEFAULT_TERMINAL id defv -> ()
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id r defv -> ()

and items_lemma (#ids: _) (ls: asn1_gen_items_l ids)
: Lemma
  (requires (wf_items ls))
  (ensures (items_psound (asn1_sequence_as_parser ls)))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    dec_lemma dk;
    items_lemma tl
#pop-options

(* Encodable values are canonical *)

let encodable_canonical (#s: _) (k: asn1_k s) (u: squash (wf k)) (x: asn1_t k)
: Lemma
  (requires (encodable k x))
  (ensures (canonical k x == true))
= top_lemma k

let check_ser_forget_encodable (#s: _) (k: asn1_k s) (u: squash (wf k)) (x: asn1_t k)
: Lemma
  (requires (encodable k x))
  (ensures (check_ser k u (forget k x) == Some x))
= encodable_canonical k u x;
  check_ser_forget k u x
