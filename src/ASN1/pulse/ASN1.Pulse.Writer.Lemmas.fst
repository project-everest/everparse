module ASN1.Pulse.Writer.Lemmas

(* Encoding equations for the right-to-left writers (ASN1.Pulse.Writer):
   the generic encoding of the generic value of each part of a schema, and
   how it decomposes along the schema. *)

open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Spec.ToValue

module Seq = FStar.Seq
module SB = LowParse.Spec.Base
module Conf = ASN1.Spec.Conformance
module WL = ASN1.Pulse.WriteLeaf
module RS = ASN1.Pulse.RelShare
module PSet = ASN1.Pulse.ParseSet
module PS = ASN1.Pulse.ParseSequence
module TS = ASN1.Spec.ToValue.Set
module W = LowParse.Pulse.R2L
module LP = FStar.List.Tot.Properties

(* Encoders *)

let cenc (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k) : GTot SB.bytes =
  asn1_value_enc (content_to_value id k x)

let kenc (#s: _) (k: asn1_k s) (x: asn1_t k) : GTot SB.bytes =
  asn1_value_enc (to_value k x)

let lcenc (lc: list (asn1_id_t & asn1_content_k)) (v: make_gen_choice_type (asn1_lc_t lc)) : GTot SB.bytes =
  let (| id, y |) = v in
  asn1_value_enc (choice_to_value lc id y)

let denc (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk) : GTot SB.bytes =
  asn1_value_list_enc (dec_to_values dk x)

let ienc (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items) : GTot SB.bytes =
  asn1_value_list_enc (items_to_values items x)

(* Generic encoders of options, defaults and pairs *)

let option_enc (#u: Type) (enc: u -> GTot SB.bytes) (y: option u) : GTot SB.bytes =
  match y with
  | None -> Seq.empty
  | Some z -> enc z

let default_enc (#u: eqtype) (#defv: u) (enc: u -> GTot SB.bytes) (y: default_tv defv) : GTot SB.bytes =
  match y with
  | Default -> Seq.empty
  | Nondefault z -> enc z

let pair_enc (#u1 #u2: Type) (enc1: u1 -> GTot SB.bytes) (enc2: u2 -> GTot SB.bytes) (y: u1 & u2) : GTot SB.bytes =
  enc1 (fst y) `Seq.append` enc2 (snd y)

(* Value lists *)

let rec value_list_enc_append (l1 l2: list asn1_value)
: Lemma (ensures asn1_value_list_enc (l1 `List.Tot.append` l2) == asn1_value_list_enc l1 `Seq.append` asn1_value_list_enc l2)
  (decreases l1)
= match l1 with
  | [] -> assert (Seq.equal (Seq.append Seq.empty (asn1_value_list_enc l2)) (asn1_value_list_enc l2))
  | a :: q -> value_list_enc_append q l2; Seq.append_assoc (asn1_value_enc a) (asn1_value_list_enc q) (asn1_value_list_enc l2)

let value_list_enc_single (v: asn1_value)
: Lemma (asn1_value_list_enc [v] == asn1_value_enc v)
= assert (Seq.equal (Seq.append (asn1_value_enc v) Seq.empty) (asn1_value_enc v))

let mk_cons_enc (id: asn1_id_t) (l: list asn1_value)
: Lemma
  (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f))
  (ensures (asn1_value_enc (mk_cons id l) == enc_tlv id true (asn1_value_list_enc l)))
= ()

let rec list_enc (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (ensures asn1_value_list_enc (list_to_values k l) == W.enc_list (kenc k) l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> list_enc k q

(* Contents *)

let cenc_terminal (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_content_t (ASN1_TERMINAL k))
: Lemma (cenc id (ASN1_TERMINAL k) x == WL.terminal_enc id k x)
= ()

let cenc_restricted (id: asn1_id_t) (k: asn1_terminal_k) (r: asn1_restriction k) (x: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
: Lemma (cenc id (ASN1_RESTRICTED_TERMINAL k r) x == WL.terminal_enc id k (RS.restricted_up k r x))
= ()

let cenc_prefixed (id: asn1_id_t) (#s: _) (k: asn1_k s) (x: asn1_content_t (ASN1_PREFIXED k))
: Lemma (cenc id (ASN1_PREFIXED k) x == asn1_value_enc (mk_encap id (to_value k x)))
= ()

let cenc_sequence (id: asn1_id_t) (g: asn1_gen_items_lk) (x: asn1_content_t (ASN1_SEQUENCE g))
: Lemma
  (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f))
  (ensures (cenc id (ASN1_SEQUENCE g) x == enc_tlv id true (ienc (dsnd g) x)))
= let (| _, items |) = g in
  mk_cons_enc id (items_to_values items x)

let cenc_seq_of (id: asn1_id_t) (ne: bool) (#s: _) (k: asn1_k s) (x: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma
  (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f))
  (ensures (cenc id (ASN1_SEQUENCE_OF ne k) x == enc_tlv id true (W.enc_list (kenc k) (RS.seq_of_up ne k x))))
= mk_cons_enc id (list_to_values k (RS.seq_of_up ne k x));
  list_enc k (RS.seq_of_up ne k x)

let cenc_set_of (id: asn1_id_t) (ne: bool) (#s: _) (k: asn1_k s) (x: asn1_content_t (ASN1_SET_OF ne k))
: Lemma
  (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f))
  (ensures (cenc id (ASN1_SET_OF ne k) x == enc_tlv id true (W.enc_list (kenc k) (RS.set_of_up ne k x))))
= mk_cons_enc id (list_to_values k (RS.set_of_up ne k x));
  list_enc k (RS.set_of_up ne k x)

(* Tags, CHOICE and ANY *)

let kenc_ilc (id: asn1_id_t) (k: asn1_content_k) (x: asn1_t (ASN1_ILC id k))
: Lemma (kenc (ASN1_ILC id k) x == cenc id k x)
= ()

let kenc_choice (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (x: asn1_t (ASN1_CHOICE_ILC lc pf))
: Lemma (kenc (ASN1_CHOICE_ILC lc pf) x == lcenc lc x)
= ()

let kenc_any (x: asn1_t ASN1_ANY_ILC)
: Lemma (kenc ASN1_ANY_ILC x == asn1_value_enc x)
= ()

let lcenc_head (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: tl)))
: Lemma
  (requires (dfst v == id'))
  (ensures (lcenc ((id', c) :: tl) v == cenc id' c (RS.lc_head_val id' c tl v ())))
= let (| id, y |) = v in
  assert_norm (choice_to_value ((id', c) :: tl) id y == (if id = id' then content_to_value id c y else choice_to_value tl id y))

let lcenc_tail (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t (hd :: tl)))
: Lemma
  (requires (dfst v <> fst hd))
  (ensures (lcenc (hd :: tl) v == lcenc tl (RS.lc_tail_val hd tl v ())))
= let (| id, y |) = v in
  let (id', c) = hd in
  assert_norm (choice_to_value ((id', c) :: tl) id y == (if id = id' then content_to_value id c y else choice_to_value tl id y));
  assert_norm (RS.lc_tail_val (id', c) tl (| id, y |) () == (| id, y |))

(* Decorated items *)

let denc_plain (#s: _) (k: asn1_k s) (x: asn1_decorated_t_core (ASN1_PLAIN_ILC k))
: Lemma (denc (ASN1_PLAIN_ILC k) x == kenc k x)
= value_list_enc_single (to_value k x)

let denc_option (#s: _) (k: asn1_k s) (x: asn1_decorated_t_core (ASN1_OPTION_ILC k))
: Lemma (denc (ASN1_OPTION_ILC k) x == option_enc (kenc k) x)
= let x' : option (asn1_t k) = x in
  match x' with
  | None -> ()
  | Some y -> value_list_enc_single (to_value k y)

let denc_default (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_terminal_t k) (x: asn1_decorated_t_core (ASN1_DEFAULT_TERMINAL id0 defv))
: Lemma (denc (ASN1_DEFAULT_TERMINAL id0 defv) x == default_enc #_ #defv (WL.terminal_enc id0 k) x)
= let x' : default_tv defv = x in
  match x' with
  | Default -> ()
  | Nondefault y -> value_list_enc_single (terminal_to_value id0 k y)

let denc_default_restricted (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: parse_filter_refine (restriction_pred r)) (x: asn1_decorated_t_core (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 r defv))
: Lemma (denc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 r defv) x == default_enc #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #defv (cenc id0 (ASN1_RESTRICTED_TERMINAL k r)) x)
= let x' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x in
  match x' with
  | Default -> ()
  | Nondefault y -> value_list_enc_single (terminal_to_value id0 k y)

(* Items *)

let ienc_nil (x: asn1_sequence_t_core ASN1_GEN_ITEMS_NIL)
: Lemma (ienc ASN1_GEN_ITEMS_NIL x == Seq.empty)
= ()

let ienc_single (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_sequence_t_core (PS.single dk))
: Lemma (ienc (PS.single dk) x == denc dk x)
= ()

let ienc_cons (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (x: asn1_sequence_t_core (PS.cons2 dk dk2 tl2))
: Lemma (ienc (PS.cons2 dk dk2 tl2) x == pair_enc (denc dk) (ienc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) x)
= let x' : asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) = x in
  let (a, b) = x' in
  value_list_enc_append (dec_to_values dk a) (items_to_values (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) b)

(* SET: when the components are declared in the canonical order of their
   tags (`items_canon`), their values are already sorted, so `sort_by_tag`
   is the identity *)

let rec for_all_mem (#a: eqtype) (f: a -> Tot bool) (l: list a) (x: a)
: Lemma (requires (List.Tot.for_all f l /\ List.Tot.mem x l)) (ensures (f x)) (decreases l)
= match l with
  | y :: q -> if x = y then () else for_all_mem f q x

let vals_in (l: list asn1_value) (tags: list asn1_id_t) : prop =
  forall v . List.Tot.memP v l ==> List.Tot.mem (value_id v) tags

let terminal_value_id (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k)
: Lemma (value_id (terminal_to_value id k x) == any_id id)
= match k with
  | ASN1_PREFIXED_TERMINAL _ _ -> ()
  | _ -> ()

let content_value_id (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k)
: Lemma (value_id (content_to_value id k x) == any_id id)
= match k with
  | ASN1_TERMINAL k' -> terminal_value_id id k' x
  | ASN1_RESTRICTED_TERMINAL k' _ -> terminal_value_id id k' x
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ ofb _ _ -> (match ofb with None -> () | Some _ -> ())
  | _ -> ()

let rec choice_value_id (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (asn1_lc_t lc))
: Lemma
  (requires (Conf.wf_lc lc))
  (ensures (value_id (choice_to_value lc id y) == id /\ List.Tot.mem id (List.Tot.map fst lc)))
  (decreases lc)
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then content_value_id id c y
    else choice_value_id tl id y

let k_value_id (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma
  (requires (Conf.wf k))
  (ensures (match PSet.k_tags k with
    | Some l -> List.Tot.mem (value_id (to_value k x)) l
    | None -> True))
= match k with
  | ASN1_ILC id k' -> content_value_id id k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, y |) = x' in
    choice_value_id lc id y
  | ASN1_ANY_ILC -> ()

#push-options "--fuel 2 --ifuel 2"
let dec_vals (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk)
: Lemma
  (requires (Conf.wf_dec dk))
  (ensures (match PSet.dec_tags dk with
    | Some l -> vals_in (dec_to_values dk x) l
    | None -> True))
= match dk with
  | ASN1_PLAIN_ILC k -> k_value_id k x
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> () | Some y -> k_value_id k y)
  | ASN1_DEFAULT_TERMINAL id #k defv ->
    let x' : default_tv defv = x in
    (match x' with Default -> () | Nondefault y -> terminal_value_id id k y)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv ->
    let x' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x in
    (match x' with Default -> () | Nondefault y -> terminal_value_id id k y)
#pop-options

let vals_in_append (l1 l2: list asn1_value) (t1 t2: list asn1_id_t)
: Lemma
  (requires (vals_in l1 t1 /\ vals_in l2 t2))
  (ensures (vals_in (l1 `List.Tot.append` l2) (t1 `List.Tot.append` t2)))
= LP.append_memP_forall l1 l2;
  let prf (v: asn1_value) : Lemma (List.Tot.memP v (l1 `List.Tot.append` l2) ==> List.Tot.mem (value_id v) (t1 `List.Tot.append` t2)) =
    LP.append_mem t1 t2 (value_id v)
  in
  Classical.forall_intro prf

#push-options "--fuel 2 --ifuel 2"
let rec items_vals (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items)
: Lemma
  (requires (Conf.wf_items items))
  (ensures (match PSet.items_tags items with
    | Some l -> vals_in (items_to_values items x) l
    | None -> True))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    dec_vals dk x;
    (match PSet.dec_tags dk with
     | Some a -> LP.append_l_nil a
     | None -> ())
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    dec_vals dk a;
    items_vals tl b;
    (match PSet.dec_tags dk, PSet.items_tags tl with
     | Some ta, Some tb -> vals_in_append (dec_to_values dk a) (items_to_values tl b) ta tb
     | _ -> ())
#pop-options

let lt_all_of (v: asn1_value) (l: list asn1_value) (ta tb: list asn1_id_t)
: Lemma
  (requires (List.Tot.mem (value_id v) ta /\ vals_in l tb /\ PSet.all_lt ta tb))
  (ensures (TS.lt_all v l))
= for_all_mem (fun x -> List.Tot.for_all (fun y -> asn1_tag_lt x y) tb) ta (value_id v);
  let prf (y: asn1_value) : Lemma (List.Tot.memP y l ==> asn1_tag_lt (value_id v) (value_id y) == true) =
    if FStar.IndefiniteDescription.strong_excluded_middle (List.Tot.memP y l)
    then for_all_mem (fun y -> asn1_tag_lt (value_id v) y) tb (value_id y)
  in
  Classical.forall_intro prf

#push-options "--fuel 2 --ifuel 2"
let rec items_sorted (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items)
: Lemma
  (requires (Conf.wf_items items /\ PSet.items_canon items))
  (ensures (TS.lt_sorted (items_to_values items x)))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    TS.dec_values_len dk x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    items_sorted tl b;
    TS.dec_values_len dk a;
    dec_vals dk a;
    items_vals tl b;
    let Some ta = PSet.dec_tags dk in
    let Some tb = PSet.items_tags tl in
    match dec_to_values dk a with
    | [] -> ()
    | [v] -> lt_all_of v (items_to_values tl b) ta tb
#pop-options

let sort_canon (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items)
: Lemma
  (requires (Conf.wf_items items /\ PSet.items_canon items))
  (ensures (sort_by_tag (items_to_values items x) == items_to_values items x))
= let l = items_to_values items x in
  items_sorted items x;
  TS.sort_sorted l;
  Classical.forall_intro (TS.count_sort l);
  TS.sorted_unique l (sort_by_tag l)

let cenc_set (id: asn1_id_t) (ids: _) (items: asn1_gen_items_l ids) (pf: _) (x: asn1_content_t (ASN1_SET ids items pf))
: Lemma
  (requires (asn1_any_id_valid id /\ CONSTRUCTED? id.f /\ Conf.wf_items items /\ PSet.items_canon items))
  (ensures (cenc id (ASN1_SET ids items pf) x == enc_tlv id true (ienc items x)))
= sort_canon items x;
  mk_cons_enc id (items_to_values items x)
