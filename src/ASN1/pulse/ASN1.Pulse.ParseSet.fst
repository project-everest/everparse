module ASN1.Pulse.ParseSet
#lang-pulse

(* Zero-copy parsing of SET { ... }, restricted to components declared in
   the canonical order of their tags (X.690 8.6, 10.3): then the present
   components are encoded in their order of declaration, and the SEQUENCE
   parser on the same items applies (ASN1.Pulse.ParseSet.Lemmas.)

   Components with an ANY type have no finite set of tags, so they are
   only supported as the only component. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.ParseSequence
open ASN1.Pulse.Interpreter

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module LP = FStar.List.Tot.Properties
module In = ASN1.Pulse.Interpreter
module Sq = ASN1.Pulse.Sequence
module SL = ASN1.Pulse.ParseSet.Lemmas

(* The tags of a component, if finitely many *)

[@@asn1_pulse_attr]
let k_tags (#s: _) (k: asn1_k s) : Tot (option (list asn1_id_t)) =
  match k with
  | ASN1_ILC id _ -> Some [id]
  | ASN1_CHOICE_ILC lc _ -> Some (List.Tot.map fst lc)
  | ASN1_ANY_ILC -> None

[@@asn1_pulse_attr]
let dec_tags (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot (option (list asn1_id_t)) =
  match dk with
  | ASN1_PLAIN_ILC k -> k_tags k
  | ASN1_OPTION_ILC k -> k_tags k
  | ASN1_DEFAULT_TERMINAL id0 _ -> Some [id0]
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 _ _ -> Some [id0]

[@@asn1_pulse_attr]
let rec items_tags (#i: _) (ls: asn1_gen_items_l i) : Tot (option (list asn1_id_t)) (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> Some []
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    match dec_tags dk, items_tags tl with
    | Some a, Some b -> Some (List.Tot.append a b)
    | _ -> None

[@@asn1_pulse_attr]
let all_lt (a b: list asn1_id_t) : Tot bool =
  List.Tot.for_all (fun x -> List.Tot.for_all (fun y -> asn1_tag_lt x y) b) a

(* Whether the components are declared in canonical order *)

[@@asn1_pulse_attr]
let rec items_canon (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ _ _ ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    items_canon tl &&
    (match dec_tags dk, items_tags tl with
     | Some a, Some b -> all_lt a b
     | _ -> false)

let rec as_set'_mem (l: list asn1_id_t) (x: asn1_id_t)
: Lemma (Set.mem x (Set.as_set' l) <==> List.Tot.mem x l)
= match l with
  | [] -> ()
  | _ :: q -> as_set'_mem q x

let dec_tags_ok (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (match dec_tags dk with
    | Some l -> forall x . Set.mem x s <==> List.Tot.mem x l
    | None -> True)
= let k_ok (#s: _) (k: asn1_k s) : Lemma (match k_tags k with
      | Some l -> forall x . Set.mem x s <==> List.Tot.mem x l
      | None -> True)
  = match k with
    | ASN1_CHOICE_ILC lc _ ->
      let l = List.Tot.map fst lc in
      FStar.Pervasives.normalize_term_spec (Set.as_set' l);
      Classical.forall_intro (as_set'_mem l)
    | _ -> ()
  in
  match dk with
  | ASN1_PLAIN_ILC k -> k_ok k
  | ASN1_OPTION_ILC k -> k_ok k
  | _ -> ()

let rec items_tags_ok (#i: _) (ls: asn1_gen_items_l i)
: Lemma
  (ensures (match items_tags ls with
    | Some l -> forall x . Set.mem x (SL.items_set (In.twins_of ls)) <==> List.Tot.mem x l
    | None -> True))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    twin_d_eq dk;
    dec_tags_ok dk;
    items_tags_ok tl;
    match dec_tags dk, items_tags tl with
    | Some a, Some b -> Classical.forall_intro (fun x -> LP.append_mem a b x <: Lemma (List.Tot.mem x (a @ b) <==> (List.Tot.mem x a || List.Tot.mem x b)))
    | _ -> ()

let rec for_all_mem (#a: eqtype) (f: a -> Tot bool) (l: list a)
: Lemma (List.Tot.for_all f l <==> (forall x . List.Tot.mem x l ==> f x))
= match l with
  | [] -> ()
  | _ :: q -> for_all_mem f q

let all_lt_ok (a b: list asn1_id_t)
: Lemma
  (requires (all_lt a b))
  (ensures (forall x y . (List.Tot.mem x a /\ List.Tot.mem y b) ==> asn1_tag_lt x y))
= for_all_mem (fun x -> List.Tot.for_all (fun y -> asn1_tag_lt x y) b) a;
  let prf (x: asn1_id_t) : Lemma (List.Tot.mem x a ==> (forall y . List.Tot.mem y b ==> asn1_tag_lt x y)) =
    for_all_mem (fun y -> asn1_tag_lt x y) b
  in
  Classical.forall_intro prf

let rec items_canon_ok (#i: _) (ls: asn1_gen_items_l i)
: Lemma
  (requires (items_canon ls))
  (ensures (SL.set_canon (In.twins_of ls)))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    items_canon_ok tl;
    twin_d_eq dk;
    dec_tags_ok dk;
    items_tags_ok tl;
    let Some a = dec_tags dk in
    let Some b = items_tags tl in
    all_lt_ok a b

(* The SET content parser *)

let set_content (#ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids)) (w: SB.bytes) (v: asn1_content_t (ASN1_SET ids items pf))
: Lemma
  (requires (items_canon items /\ parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf)) w v))
  (ensures (seq_parsed_core items w v))
= let _ = seq_t_eq items in
  items_canon_ok items;
  ASN1.Spec.Conformance.items_tagged_intro items;
  SL.set_seq_parsed (In.twins_of items) w (coerce_eq (seq_t_eq items) v)

inline_for_extraction
fn set_parser
  (#ids: Ghost.erased id_decs)
  (items: Ghost.erased (asn1_gen_items_l ids))
  (pf: squash (asn1_set_k_wf ids))
  (u: squash (items_canon (Ghost.reveal items)))
  (#t: Type0) (di: Ghost.erased (idesc (Ghost.reveal items) t))
  (f: sparser di)
: aparser #t #(asn1_sequence_t_core (Ghost.reveal items)) (irel di) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  set_content items pf w v;
  f input #pm #w #v
}
