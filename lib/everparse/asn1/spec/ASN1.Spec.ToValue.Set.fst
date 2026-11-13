module ASN1.Spec.ToValue.Set

(* SET: the elements of a SET, as parsed, are in strictly increasing tag
   order, so their generic values are exactly `sort_by_tag` of the
   generic values of the components in declaration order. *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List
open LowParse.Tot.VLGen
open LowParse.Tot.Defaultable

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.LengthU32
open ASN1.Spec.Value
open ASN1.Spec.Value.Enc
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Spec.Any
open ASN1.Spec.Set
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue

module U32 = FStar.UInt32
module Seq = FStar.Seq
open ASN1.Spec.ToValue.Sound

module IDE = FStar.IndefiniteDescription

(* Generic values of SET elements *)

let rec elem_values (its: list gen_decorated_parser_twin) (e: set_elem_t its) : GTot (list asn1_value) (decreases its) =
  match its with
  | hd :: tl ->
    let e0 : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
    match e0 with
    | Inl v -> item_values hd v
    | Inr e' -> elem_values tl e'

let rec concat_values (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) : GTot (list asn1_value) (decreases l) =
  match l with
  | [] -> []
  | e :: q -> elem_values its e `List.append` concat_values its q

let elem_ok (its: list gen_decorated_parser_twin) (e: set_elem_t its) : GTot prop =
  match elem_values its e, elem_tag its e with
  | [w], Some t -> value_id w == t
  | _ -> False

let rec elems_ok (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) : GTot prop (decreases l) =
  match l with
  | [] -> True
  | e :: q -> elem_ok its e /\ elems_ok its q

#push-options "--fuel 2 --ifuel 2"
let dec_values_len (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk)
: Lemma (List.length (dec_to_values dk x) <= 1)
= match dk with
  | ASN1_PLAIN_ILC _ -> ()
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> () | Some _ -> ())
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x' : default_tv defv = x in
    (match x' with Default -> () | Nondefault _ -> ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x in
    (match x' with Default -> () | Nondefault _ -> ())

let item_values_len (it: gen_decorated_parser_twin) (x: asn1_decorated_t (Mkgendcparser?.d it))
: Lemma (List.length (item_values it x) <= 1)
= match it with
  | Mkgendcparser d _ _ ->
    let (| _, _, dk |) = d in
    dec_values_len dk x

let rec elem_values_len (its: list gen_decorated_parser_twin) (e: set_elem_t its)
: Lemma (ensures (List.length (elem_values its e) <= 1)) (decreases its)
= match its with
  | hd :: tl ->
    let e0 : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
    match e0 with
    | Inl v -> item_values_len hd v
    | Inr e' -> elem_values_len tl e'
#pop-options

#push-options "--fuel 0 --ifuel 1"
let asn1_id_enc_nonempty (id: asn1_id_t)
: Lemma (Seq.length (asn1_id_enc id) > 0)
= let MK_ASN1_ID c f n = id in
  if U32.v n < 31
  then assert (Seq.length (asn1_id_enc id) == 1)
  else assert (Seq.length (asn1_id_enc id) == 1 + Seq.length (enc_long n))
#pop-options

#push-options "--fuel 2 --ifuel 1"
let elem_values_shape (its: list gen_decorated_parser_twin) (e: set_elem_t its) (id: asn1_id_t) (c: bytes)
: Lemma
  (requires (asn1_id_enc id `Seq.append` c == asn1_value_list_enc (elem_values its e) /\ elem_tag its e == Some id))
  (ensures (elem_ok its e))
= elem_values_len its e;
  asn1_id_enc_nonempty id;
  match elem_values its e with
  | [] -> ()
  | [w] ->
    list_enc_single w;
    value_enc_eq w;
    asn1_id_enc_prefix_free id (value_id w) c (enc_hdr (value_ok w) (Seq.length (value_contents w)) `Seq.append` value_contents w)
#pop-options

(* Parsing one element, then a list of elements *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec set_elem_twin_v (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (items_esound its))
  (ensures (match parse (parse_set_elem_twin its id) b with
    | Some (e, n) -> asn1_id_enc id `Seq.append` Seq.slice b 0 n == asn1_value_list_enc (elem_values its e)
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    if FStar.Set.mem id s
    then begin
      item_twin_v hd id b;
      parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b
    end
    else begin
      set_elem_twin_v tl id b;
      parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b
    end
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_elem_v (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_esound its /\ items_tagged its))
  (ensures (match parse (parse_set_elem its) b with
    | Some (e, n) -> Seq.slice b 0 n == asn1_value_list_enc (elem_values its e) /\ elem_ok its e
    | None -> True))
= parse_set_elem_twin_cases_injective its;
  and_then_eq parse_asn1_identifier_U32 (parse_set_elem_twin its) b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    parse_asn1_identifier_U32_consumed b;
    set_elem_twin_v its id b1;
    set_elem_twin_tag its id b1;
    (match parse (parse_set_elem_twin its id) b1 with
     | Some (e, n2) ->
       slice_split b c1 n2;
       elem_values_shape its e id (Seq.slice b1 0 n2)
     | None -> ())
  | None -> ()
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec set_list_v (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_esound its /\ items_tagged its))
  (ensures (match parse (parse_list (parse_set_elem its)) b with
    | Some (l, n) -> Seq.slice b 0 n == asn1_value_list_enc (concat_values its l) /\ elems_ok its l
    | None -> True))
  (decreases (Seq.length b))
= let p = parse_set_elem its in
  tot_parse_list_eq p b;
  if Seq.length b = 0
  then Seq.lemma_eq_elim (Seq.slice b 0 0) Seq.empty
  else match parse p b with
  | Some (e, c) ->
    set_elem_v its b;
    if c > 0 then begin
      let b' = Seq.slice b c (Seq.length b) in
      set_list_v its b';
      match parse (parse_list p) b' with
      | Some (l', n2) ->
        slice_split b c n2;
        list_enc_append (elem_values its e) (concat_values its l')
      | None -> ()
    end
  | None -> ()
#pop-options

(* The wire list is strictly sorted *)

let rec lt_adj (l: list asn1_value) : Tot prop (decreases l) =
  match l with
  | a :: b :: q -> asn1_tag_lt (value_id a) (value_id b) == true /\ lt_adj (b :: q)
  | _ -> True

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec wire_adj (its: list gen_decorated_parser_twin) (l: list (set_elem_t its))
: Lemma
  (requires (tags_sorted (elem_tag its) l /\ elems_ok its l))
  (ensures (lt_adj (concat_values its l)))
  (decreases l)
= match l with
  | [] -> ()
  | [e] ->
    let [w] = elem_values its e in
    assert (concat_values its l == [w])
  | e1 :: e2 :: q ->
    wire_adj its (e2 :: q);
    let [w1] = elem_values its e1 in
    let [w2] = elem_values its e2 in
    assert (concat_values its l == w1 :: concat_values its (e2 :: q));
    assert (concat_values its (e2 :: q) == w2 :: concat_values its q)
#pop-options

let lt_all (v: asn1_value) (l: list asn1_value) : prop =
  forall y. List.memP y l ==> asn1_tag_lt (value_id v) (value_id y) == true

let rec lt_sorted (l: list asn1_value) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: q -> lt_all x q /\ lt_sorted q

let rec lt_adj_sorted (l: list asn1_value)
: Lemma (requires (lt_adj l)) (ensures (lt_sorted l)) (decreases l)
= match l with
  | [] -> ()
  | [_] -> ()
  | a :: b :: q -> lt_adj_sorted (b :: q)

(* sort_by_tag is sorted *)

let le_all (v: asn1_value) (l: list asn1_value) : prop =
  forall y. List.memP y l ==> asn1_tag_lt (value_id y) (value_id v) == false

let rec le_sorted (l: list asn1_value) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: q -> le_all x q /\ le_sorted q

let rec insert_mem (v: asn1_value) (l: list asn1_value)
: Lemma (ensures (forall y. List.memP y (insert_by_tag v l) <==> (y == v \/ List.memP y l))) (decreases l)
= match l with
  | [] -> ()
  | w :: q -> insert_mem v q

let rec insert_sorted (v: asn1_value) (l: list asn1_value)
: Lemma (requires (le_sorted l)) (ensures (le_sorted (insert_by_tag v l))) (decreases l)
= match l with
  | [] -> ()
  | w :: q ->
    if asn1_tag_lt (value_id w) (value_id v)
    then begin
      insert_sorted v q;
      insert_mem v q
    end
    else ()

let rec sort_sorted (l: list asn1_value)
: Lemma (ensures (le_sorted (sort_by_tag l))) (decreases l)
= match l with
  | [] -> ()
  | v :: q -> sort_sorted q; insert_sorted v (sort_by_tag q)

(* Multiplicities *)

let rec count (x: asn1_value) (l: list asn1_value) : GTot nat (decreases l) =
  match l with
  | [] -> 0
  | y :: q -> (if IDE.strong_excluded_middle (x == y) then 1 else 0) + count x q

let rec count_append (x: asn1_value) (l1 l2: list asn1_value)
: Lemma (ensures (count x (l1 `List.append` l2) == count x l1 + count x l2)) (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> count_append x q l2

let rec count_mem (x: asn1_value) (l: list asn1_value)
: Lemma (ensures (count x l > 0 <==> List.memP x l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> count_mem x q

let rec count_insert (x: asn1_value) (v: asn1_value) (l: list asn1_value)
: Lemma (ensures (count x (insert_by_tag v l) == count x (v :: l))) (decreases l)
= match l with
  | [] -> ()
  | w :: q -> count_insert x v q

let rec count_sort (l: list asn1_value) (x: asn1_value)
: Lemma (ensures (count x (sort_by_tag l) == count x l)) (decreases l)
= match l with
  | [] -> ()
  | v :: q -> count_sort q x; count_insert x v (sort_by_tag q)

(* A strictly sorted list is the only sorted permutation of itself *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let rec sorted_unique (w t: list asn1_value)
: Lemma
  (requires (lt_sorted w /\ le_sorted t /\ (forall x. count x w == count x t)))
  (ensures (w == t))
  (decreases w)
= match w, t with
  | [], [] -> ()
  | [], y :: _ -> assert (count y t > 0); assert (count y w == 0)
  | a :: _, [] -> assert (count a w > 0); assert (count a t == 0)
  | a :: w', b :: t' ->
    if IDE.strong_excluded_middle (a == b)
    then begin
      let prf (x: asn1_value) : Lemma (count x w' == count x t') =
        assert (count x w == count x t)
      in
      Classical.forall_intro prf;
      sorted_unique w' t'
    end
    else begin
      assert (count b w == count b t);
      count_mem b w; count_mem b t;
      count_mem a w; count_mem a t;
      assert (count a w == count a t);
      assert (List.memP b w');
      assert (List.memP a t')
    end
#pop-options

(* The wire list is a permutation of the declaration-order list *)

let rec items_list_values (hd: gen_decorated_parser_twin) (h: list (asn1_decorated_t (Mkgendcparser?.d hd))) : GTot (list asn1_value) (decreases h) =
  match h with
  | [] -> []
  | v :: q -> item_values hd v `List.append` items_list_values hd q

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec concat_split (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (l: list (set_elem_t (hd :: tl))) (x: asn1_value)
: Lemma
  (ensures (
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
    count x (concat_values (hd :: tl) l) == count x (items_list_values hd (heads l')) + count x (concat_values tl (tails l'))))
  (decreases l)
= let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
  match l' with
  | [] -> ()
  | e :: q ->
    concat_split hd tl q x;
    count_append x (elem_values (hd :: tl) e) (concat_values (hd :: tl) q);
    match e with
    | Inl v -> count_append x (item_values hd v) (items_list_values hd (heads q))
    | Inr e' -> count_append x (elem_values tl e') (concat_values tl (tails q))

let comp_values (hd: gen_decorated_parser_twin) (h: list (asn1_decorated_t (Mkgendcparser?.d hd)) { comp_ok hd h })
: Lemma (items_list_values hd h == item_values hd (comp_value hd h))
= match h with
  | [v] -> List.append_l_nil (item_values hd v)
  | [] -> item_default_values hd

let empty_elems (l: list (set_elem_t []))
: Lemma (l == [])
= match l with
  | [] -> ()
  | _ :: _ -> ()

let rec set_perm (its: list gen_decorated_parser_twin) (l: list (set_elem_t its) { comps_ok its l }) (x: asn1_value)
: Lemma
  (ensures (count x (concat_values its l) == count x (seq_values its (set_to_tuple' its l))))
  (decreases its)
= match its with
  | [] -> empty_elems l
  | [hd] ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t [])) = l in
    concat_split hd [] l x;
    empty_elems (tails l');
    comp_values hd (heads l')
  | hd :: tl ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
    concat_split hd tl l x;
    comp_values hd (heads l');
    set_perm tl (tails l') x;
    let v = comp_value hd (heads l') in
    let r = set_to_tuple' tl (tails l') in
    assert (set_to_tuple' its l == (v, r));
    count_append x (item_values hd v) (seq_values tl r)
#pop-options

(* The SET parser *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_parser_esound (its: list gen_decorated_parser_twin)
: Lemma
  (requires (items_esound its /\ items_tagged its))
  (ensures (esound (make_asn1_set_parser its) (fun x -> asn1_value_list_enc (sort_by_tag (seq_values its x)))))
= set_to_tuple_injective its;
  let pl = parse_list (parse_set_elem its) in
  let pf = pl `parse_filter` set_ok its in
  let prf (b: bytes) : Lemma (match parse (make_asn1_set_parser its) b with
    | Some (x, n) -> Seq.slice b 0 n == asn1_value_list_enc (sort_by_tag (seq_values its x))
    | None -> True)
  = parse_synth_eq pf (set_to_tuple its) b;
    parse_filter_eq pl (set_ok its) b;
    set_list_v its b;
    match parse pl b with
    | Some (l, n) ->
      if set_ok its l
      then begin
        let w = concat_values its l in
        let s = seq_values its (set_to_tuple its l) in
        wire_adj its l;
        lt_adj_sorted w;
        sort_sorted s;
        Classical.forall_intro (set_perm its l);
        Classical.forall_intro (count_sort s);
        sorted_unique w (sort_by_tag s)
      end
    | None -> ()
  in
  Classical.forall_intro prf
#pop-options
