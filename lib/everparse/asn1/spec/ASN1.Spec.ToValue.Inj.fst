module ASN1.Spec.ToValue.Inj

(* Injectivity of `to_value` on well-formed schemas: a typed value is
   determined by its generic value.  Hence a typed value is encodable as
   soon as its generic value conforms to the schema. *)

open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.Value.Enc
open ASN1.Spec.Content.Enc
open ASN1.Spec.Interpreter
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue
open ASN1.Spec.Serializer

module List = FStar.List.Tot
module Set = FStar.Set
module TVS = ASN1.Spec.ToValue.Set

(* Identifiers of generic values *)

let terminal_to_value_id (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k)
: Lemma (value_id (terminal_to_value id k x) == any_id id)
= ()

let content_to_value_id (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k)
: Lemma (value_id (content_to_value id k x) == any_id id)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> terminal_to_value_id id k' x
  | ASN1_TERMINAL k' -> terminal_to_value_id id k' x
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ ofb _ _ ->
    begin match ofb with
    | None -> ()
    | Some _ -> ()
    end
  | _ -> ()

let rec choice_to_value_id (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (asn1_lc_t lc))
: Lemma
  (ensures (
    value_id (choice_to_value lc id y) == any_id id /\
    List.mem id (List.map fst lc) /\
    (wf_lc lc ==> asn1_any_id_valid id)))
  (decreases lc)
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then content_to_value_id id c y
    else choice_to_value_id tl id y

let rec mem_as_set' (#a: eqtype) (x: a) (l: list a)
: Lemma (ensures (Set.mem x (Set.as_set' l) <==> List.mem x l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> mem_as_set' x q

let to_value_mem (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma
  (requires (wf k))
  (ensures (Set.mem (value_id (to_value k x)) s))
= match k with
  | ASN1_ILC id k' -> content_to_value_id id k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, y |) = x' in
    choice_to_value_id lc id y;
    mem_as_set' id (List.map fst lc)
  | ASN1_ANY_ILC -> ()

(* The generic values of a decorated item: at most one, exactly one if
   PLAIN, with an identifier in the set of the item *)

let dec_values_ok (s: Set.set asn1_id_t) (d: asn1_decorator) (l: list asn1_value) : prop =
  List.length l <= 1 /\
  (PLAIN? d ==> List.length l == 1) /\
  (forall v . List.memP v l ==> Set.mem (value_id v) s)

let dec_values (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk)
: Lemma
  (requires (wf_dec dk))
  (ensures (dec_values_ok s d (dec_to_values dk x)))
= match dk with
  | ASN1_PLAIN_ILC k -> to_value_mem k x
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> () | Some y -> to_value_mem k y)
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x' : default_tv defv = x in
    (match x' with Default -> () | Nondefault y -> terminal_to_value_id id k y)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x in
    (match x' with Default -> () | Nondefault y -> terminal_to_value_id id k y)

(* Sequences: the identifier of the next present item is not in the set of
   the skipped OPTIONAL / DEFAULT items (asn1_sequence_k_wf) *)

let head_not_in (l: list asn1_value) (s: Set.set asn1_id_t) : prop =
  match l with
  | [] -> True
  | v :: _ -> ~ (Set.mem (value_id v) s)

let rec wf_tail (li: id_decs) (s: Set.set asn1_id_t) (r: list asn1_value) : Tot prop (decreases li) =
  match li with
  | [] -> head_not_in r s
  | (s', d) :: tl ->
    Set.disjoint s s' /\
    (match d with
     | PLAIN -> wf_tail tl Set.empty r
     | _ -> wf_tail tl (Set.union s s') r)

let union_empty_l (s: Set.set asn1_id_t)
: Lemma (Set.union Set.empty s == s)
= Set.lemma_equal_elim (Set.union Set.empty s) s

let rec seq_wf'_tail (li: id_decs) (s: Set.set asn1_id_t)
: Lemma (requires (asn1_sequence_k_wf' li s)) (ensures (wf_tail li s [])) (decreases %[li; 0])
= match li with
  | [] -> ()
  | (s', d) :: tl ->
    begin match d with
    | PLAIN -> seq_wf_tail tl
    | _ -> seq_wf'_tail tl (Set.union s s')
    end

and seq_wf_tail (li: id_decs)
: Lemma (requires (asn1_sequence_k_wf li)) (ensures (wf_tail li Set.empty [])) (decreases %[li; 1])
= match li with
  | [] -> ()
  | (s', d) :: tl ->
    begin match d with
    | PLAIN -> seq_wf_tail tl
    | _ -> union_empty_l s'; seq_wf'_tail tl s'
    end

let head_in (r: list asn1_value) (ks: Set.set asn1_id_t) : prop =
  match r with
  | [] -> False
  | v :: _ -> Set.mem (value_id v) ks

let rec any_prefix_wf'_tail (ks: Set.set asn1_id_t) (li: id_decs) (s: Set.set asn1_id_t) (r: list asn1_value)
: Lemma (requires (asn1_any_prefix_k_wf' ks li s /\ head_in r ks)) (ensures (wf_tail li s r)) (decreases %[li; 0])
= match li with
  | [] -> ()
  | (s', d) :: tl ->
    begin match d with
    | PLAIN -> any_prefix_wf_tail ks tl r
    | _ -> any_prefix_wf'_tail ks tl (Set.union s s') r
    end

and any_prefix_wf_tail (ks: Set.set asn1_id_t) (li: id_decs) (r: list asn1_value)
: Lemma (requires (asn1_any_prefix_k_wf ks li /\ head_in r ks)) (ensures (wf_tail li Set.empty r)) (decreases %[li; 1])
= match li with
  | [] -> ()
  | (s', d) :: tl ->
    begin match d with
    | PLAIN -> any_prefix_wf_tail ks tl r
    | _ -> union_empty_l s'; any_prefix_wf'_tail ks tl s' r
    end

let dec_head_not_in (s s': Set.set asn1_id_t) (d: asn1_decorator) (l r: list asn1_value)
: Lemma
  (requires (dec_values_ok s' d l /\ Set.disjoint s s' /\ (l == [] ==> head_not_in r (Set.union s s'))))
  (ensures (head_not_in (l `List.append` r) s))
= match l with
  | [] -> ()
  | v :: _ -> assert (List.memP v l)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec items_head (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (x: asn1_sequence_t_core items) (r: list asn1_value)
: Lemma
  (requires (wf_items items /\ wf_tail ids s r))
  (ensures (head_not_in (items_to_values items x `List.append` r) s))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    dec_values dk x;
    dec_head_not_in s s' d (dec_to_values dk x) r
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    dec_values dk a;
    List.append_assoc (dec_to_values dk a) (items_to_values tl b) r;
    if Nil? (dec_to_values dk a) then items_head tl (Set.union s s') b r;
    dec_head_not_in s s' d (dec_to_values dk a) (items_to_values tl b `List.append` r)

let rec any_sfx (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (x: asn1_sequence_any_t_core items sfx_t)
: Tot sfx_t (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    snd x'
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    any_sfx tl (snd x')

let rec items_any_head (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (x: asn1_sequence_any_t_core items sfx_t)
: Lemma
  (requires (wf_items items /\ (forall (y: sfx_t) . wf_tail ids s (sfx y))))
  (ensures (head_not_in (items_any_to_values items sfx x) s))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    let (a, b) = x' in
    dec_values dk a;
    dec_head_not_in s s' d (dec_to_values dk a) (sfx b)
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    let (a, b) = x' in
    assert (wf_tail ids s (sfx (any_sfx tl b)));
    dec_values dk a;
    if Nil? (dec_to_values dk a) then items_any_head tl (Set.union s s') sfx b;
    dec_head_not_in s s' d (dec_to_values dk a) (items_any_to_values tl sfx b)
#pop-options

(* Splitting the values of one item from the following ones *)

let split_dec (s s': Set.set asn1_id_t) (d: asn1_decorator) (l1 l2 r1 r2: list asn1_value)
: Lemma
  (requires (
    dec_values_ok s' d l1 /\ dec_values_ok s' d l2 /\
    (l1 == [] ==> head_not_in r1 (Set.union s s')) /\
    (l2 == [] ==> head_not_in r2 (Set.union s s')) /\
    l1 `List.append` r1 == l2 `List.append` r2))
  (ensures (l1 == l2 /\ r1 == r2))
= match l1, l2 with
  | [], [] -> ()
  | [], v :: _ -> assert (List.memP v l2)
  | v :: _, [] -> assert (List.memP v l1)
  | _ :: _, _ :: _ -> ()

(* Multisets of values of length at most one *)

let short_count_eq (l1 l2: list asn1_value)
: Lemma
  (requires (List.length l1 <= 1 /\ List.length l2 <= 1 /\ (forall v . TVS.count v l1 == TVS.count v l2)))
  (ensures (l1 == l2))
= match l1, l2 with
  | [], [] -> ()
  | [a], [] -> assert (TVS.count a l1 == TVS.count a l2)
  | [], [b] -> assert (TVS.count b l1 == TVS.count b l2)
  | [a], [b] -> assert (TVS.count a l1 == TVS.count a l2)

let rec count_not_mem (v: asn1_value) (l: list asn1_value) (p: asn1_value -> GTot prop)
: Lemma
  (requires ((forall w . List.memP w l ==> p w) /\ ~ (p v)))
  (ensures (TVS.count v l == 0))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> count_not_mem v q p

(* SET components have distinct tags (asn1_set_k_wf) *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec set_items_not_in (#ids: _) (items: asn1_gen_items_l ids) (s0: Set.set asn1_id_t) (x: asn1_sequence_t_core items)
: Lemma
  (requires (wf_items items /\ asn1_set_k_wf' s0 ids))
  (ensures (forall v . List.memP v (items_to_values items x) ==> ~ (Set.mem (value_id v) s0)))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    dec_values dk x;
    assert (forall (i: asn1_id_t) . asn1_same_tag i i)
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    dec_values dk a;
    set_items_not_in tl s0 b;
    assert (forall (i: asn1_id_t) . asn1_same_tag i i);
    FStar.Classical.forall_intro (List.append_memP (dec_to_values dk a) (items_to_values tl b))
#pop-options

(* Main theorem *)

let choice_precedes (id: asn1_id_t) (c: asn1_content_k) (tl lc: list (asn1_id_t & asn1_content_k))
: Lemma (requires (lc == (id, c) :: tl)) (ensures (c << lc))
= ()

let mk_encap_inj (id: asn1_id_t) (w1 w2: asn1_value)
: Lemma (requires (mk_encap id w1 == mk_encap id w2)) (ensures (w1 == w2))
= if CONSTRUCTED? id.f
  then ()
  else asn1_value_enc_inj w1 w2

let rec terminal_inj (id: asn1_id_t) (k: asn1_terminal_k) (x1 x2: asn1_terminal_t k)
: Lemma
  (requires (terminal_to_value id k x1 == terminal_to_value id k x2))
  (ensures (x1 == x2))
  (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_t k2);
    let x1' : asn1_terminal_t k2 = FStar.Pervasives.coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k2) () x1 in
    let x2' : asn1_terminal_t k2 = FStar.Pervasives.coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k2) () x2 in
    mk_encap_inj id (terminal_to_value id2 k2 x1') (terminal_to_value id2 k2 x2');
    terminal_inj id2 k2 x1' x2'
  | _ -> leaf_enc_inj k x1 x2

let adb_sfx_t (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Type =
  make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)

let adb_fb_sfx_t (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fbids: id_decs) (fbitems: asn1_gen_items_l fbids) : Type =
  make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)

let fb_precedes' (k: asn1_content_k)
: Lemma
  (requires (ASN1_ANY_DEFINED_BY? k /\ Some? (ASN1_ANY_DEFINED_BY?.fallback k)))
  (ensures (dsnd (Some?.v (ASN1_ANY_DEFINED_BY?.fallback k)) << k))
= match k with
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ (Some fb) _ _ -> ()

let fb_precedes
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
: Lemma (fbitems << ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf')
= fb_precedes' (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf')

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"
let rec to_value_inj (#s: _) (k: asn1_k s) (x1 x2: asn1_t k)
: Lemma
  (requires (wf k /\ to_value k x1 == to_value k x2))
  (ensures (x1 == x2))
  (decreases %[k; 2])
= match k with
  | ASN1_ILC id k' -> content_inj id k' x1 x2
  | ASN1_CHOICE_ILC lc _ ->
    let x1' : make_gen_choice_type (asn1_lc_t lc) = x1 in
    let x2' : make_gen_choice_type (asn1_lc_t lc) = x2 in
    let (| id1, y1 |) = x1' in
    let (| id2, y2 |) = x2' in
    choice_to_value_id lc id1 y1;
    choice_to_value_id lc id2 y2;
    choice_inj lc id1 y1 y2
  | ASN1_ANY_ILC -> ()

and content_inj (id: asn1_id_t) (k: asn1_content_k) (x1 x2: asn1_content_t k)
: Lemma
  (requires (wf_content id k /\ content_to_value id k x1 == content_to_value id k x2))
  (ensures (x1 == x2))
  (decreases %[k; 1])
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> terminal_inj id k' x1 x2
  | ASN1_TERMINAL k' -> terminal_inj id k' x1 x2
  | ASN1_SEQUENCE gitems ->
    let (| ids, items |) = gitems in
    seq_wf_tail ids;
    List.append_l_nil (items_to_values items x1);
    List.append_l_nil (items_to_values items x2);
    items_split items Set.empty x1 x2 [] []
  | ASN1_SET ids items _ ->
    let l1 = items_to_values items x1 in
    let l2 = items_to_values items x2 in
    let prf (v: asn1_value) : Lemma (TVS.count v l1 == TVS.count v l2) =
      TVS.count_sort l1 v;
      TVS.count_sort l2 v
    in
    FStar.Classical.forall_intro prf;
    set_inj items x1 x2
  | ASN1_SEQUENCE_OF _ k' -> list_inj k' x1 x2
  | ASN1_SET_OF _ k' -> list_inj k' x1 x2
  | ASN1_PREFIXED k' ->
    mk_encap_inj id (to_value k' x1) (to_value k' x2);
    to_value_inj k' x1 x2
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None -> adb_inj id idp prefix kid key_k ls pf pf' x1 x2
    | Some fb ->
      let (| fbids, fbitems |) = fb in
      adb_fb_inj id idp prefix kid key_k ls fbids fbitems pf pf' x1 x2
    end

and list_inj (#s: _) (k: asn1_k s) (l1 l2: list (asn1_t k))
: Lemma
  (requires (wf k /\ list_to_values k l1 == list_to_values k l2))
  (ensures (l1 == l2))
  (decreases %[k; 3; l1])
= match l1, l2 with
  | a1 :: q1, a2 :: q2 ->
    to_value_inj k a1 a2;
    list_inj k q1 q2
  | _ -> ()

and choice_inj (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y1 y2: idlookup_t id (asn1_lc_t lc))
: Lemma
  (requires (wf_lc lc /\ choice_to_value lc id y1 == choice_to_value lc id y2))
  (ensures (y1 == y2))
  (decreases %[lc; 0])
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    choice_precedes id' c tl lc;
    if id = id'
    then content_inj id c y1 y2
    else choice_inj tl id y1 y2

and dec_inj (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x1 x2: asn1_decorated_t_core dk)
: Lemma
  (requires (wf_dec dk /\ dec_to_values dk x1 == dec_to_values dk x2))
  (ensures (x1 == x2))
  (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> to_value_inj k x1 x2
  | ASN1_OPTION_ILC k ->
    let x1' : option (asn1_t k) = x1 in
    let x2' : option (asn1_t k) = x2 in
    (match x1', x2' with
     | Some y1, Some y2 -> to_value_inj k y1 y2
     | _ -> ())
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x1' : default_tv defv = x1 in
    let x2' : default_tv defv = x2 in
    (match x1', x2' with
     | Nondefault y1, Nondefault y2 -> terminal_inj id k y1 y2
     | _ -> ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x1' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x1 in
    let x2' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x2 in
    (match x1', x2' with
     | Nondefault y1, Nondefault y2 -> terminal_inj id k y1 y2
     | _ -> ())

and items_split (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (x1 x2: asn1_sequence_t_core items) (r1 r2: list asn1_value)
: Lemma
  (requires (
    wf_items items /\ wf_tail ids s r1 /\ wf_tail ids s r2 /\
    items_to_values items x1 `List.append` r1 == items_to_values items x2 `List.append` r2))
  (ensures (x1 == x2 /\ r1 == r2))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    dec_values dk x1;
    dec_values dk x2;
    split_dec s s' d (dec_to_values dk x1) (dec_to_values dk x2) r1 r2;
    dec_inj dk x1 x2
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let x1' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x1 in
    let x2' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x2 in
    let (a1, b1) = x1' in
    let (a2, b2) = x2' in
    dec_values dk a1;
    dec_values dk a2;
    List.append_assoc (dec_to_values dk a1) (items_to_values tl b1) r1;
    List.append_assoc (dec_to_values dk a2) (items_to_values tl b2) r2;
    if not (PLAIN? d) then begin
      items_head tl (Set.union s s') b1 r1;
      items_head tl (Set.union s s') b2 r2
    end;
    split_dec s s' d (dec_to_values dk a1) (dec_to_values dk a2) (items_to_values tl b1 `List.append` r1) (items_to_values tl b2 `List.append` r2);
    dec_inj dk a1 a2;
    let s1 : Set.set asn1_id_t = if PLAIN? d then Set.empty else Set.union s s' in
    items_split tl s1 b1 b2 r1 r2

and items_any_split (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (x1 x2: asn1_sequence_any_t_core items sfx_t)
: Lemma
  (requires (
    wf_items items /\
    (forall (y: sfx_t) . wf_tail ids s (sfx y)) /\
    (forall (y1 y2: sfx_t) . sfx y1 == sfx y2 ==> y1 == y2) /\
    items_any_to_values items sfx x1 == items_any_to_values items sfx x2))
  (ensures (x1 == x2))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let x1' : asn1_decorated_t_core dk & sfx_t = x1 in
    let x2' : asn1_decorated_t_core dk & sfx_t = x2 in
    let (a1, b1) = x1' in
    let (a2, b2) = x2' in
    dec_values dk a1;
    dec_values dk a2;
    assert (wf_tail ids s (sfx b1));
    assert (wf_tail ids s (sfx b2));
    split_dec s s' d (dec_to_values dk a1) (dec_to_values dk a2) (sfx b1) (sfx b2);
    dec_inj dk a1 a2
  | ASN1_GEN_ITEMS_CONS s' d dk tids tl ->
    let x1' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x1 in
    let x2' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x2 in
    let (a1, b1) = x1' in
    let (a2, b2) = x2' in
    assert (wf_tail ids s (sfx (any_sfx tl b1)));
    dec_values dk a1;
    dec_values dk a2;
    let s1 : Set.set asn1_id_t = if PLAIN? d then Set.empty else Set.union s s' in
    assert (forall (y: sfx_t) . wf_tail tids s1 (sfx y));
    if not (PLAIN? d) then begin
      items_any_head tl (Set.union s s') sfx b1;
      items_any_head tl (Set.union s s') sfx b2
    end;
    split_dec s s' d (dec_to_values dk a1) (dec_to_values dk a2) (items_any_to_values tl sfx b1) (items_any_to_values tl sfx b2);
    dec_inj dk a1 a2;
    items_any_split tl s1 sfx b1 b2

and set_inj (#ids: _) (items: asn1_gen_items_l ids) (x1 x2: asn1_sequence_t_core items)
: Lemma
  (requires (
    wf_items items /\ asn1_set_k_wf ids /\
    (forall v . TVS.count v (items_to_values items x1) == TVS.count v (items_to_values items x2))))
  (ensures (x1 == x2))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    dec_values dk x1;
    dec_values dk x2;
    short_count_eq (dec_to_values dk x1) (dec_to_values dk x2);
    dec_inj dk x1 x2
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let x1' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x1 in
    let x2' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x2 in
    let (a1, b1) = x1' in
    let (a2, b2) = x2' in
    let d1 = dec_to_values dk a1 in
    let d2 = dec_to_values dk a2 in
    let t1 = items_to_values tl b1 in
    let t2 = items_to_values tl b2 in
    dec_values dk a1;
    dec_values dk a2;
    set_items_not_in tl s' b1;
    set_items_not_in tl s' b2;
    let in_s' (w: asn1_value) : GTot prop = Set.mem (value_id w) s' in
    let not_in_s' (w: asn1_value) : GTot prop = ~ (Set.mem (value_id w) s') in
    let prf (v: asn1_value) : Lemma (TVS.count v d1 == TVS.count v d2 /\ TVS.count v t1 == TVS.count v t2) =
      TVS.count_append v d1 t1;
      TVS.count_append v d2 t2;
      if Set.mem (value_id v) s'
      then begin
        count_not_mem v t1 not_in_s';
        count_not_mem v t2 not_in_s'
      end else begin
        count_not_mem v d1 in_s';
        count_not_mem v d2 in_s'
      end
    in
    FStar.Classical.forall_intro prf;
    short_count_eq d1 d2;
    dec_inj dk a1 a2;
    set_inj tl b1 b2

and ls_inj (#lt #t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (key: t) (y1 y2: idlookup_t key (asn1_any_t_core t f ls))
: Lemma
  (requires (wf_ls ls /\ ls_to_values f ls key y1 == ls_to_values f ls key y2))
  (ensures (y1 == y2))
  (decreases %[ls; 0])
= match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| ids, items |) = it in
    if key = f key'
    then begin
      seq_wf_tail ids;
      List.append_l_nil (items_to_values items y1);
      List.append_l_nil (items_to_values items y2);
      items_split items Set.empty y1 y2 [] []
    end
    else ls_inj f tl key y1 y2

and ls_fb_inj (#lt #t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (fb: Type) (fbf: fb -> Tot (list asn1_value)) (key: t) (y1 y2: idlookup_with_fallback_t key (asn1_any_t_core t f ls) fb)
: Lemma
  (requires (
    wf_ls ls /\ (forall (z1 z2: fb) . fbf z1 == fbf z2 ==> z1 == z2) /\
    ls_fb_to_values f ls fb fbf key y1 == ls_fb_to_values f ls fb fbf key y2))
  (ensures (y1 == y2))
  (decreases %[ls; 0])
= match ls with
  | [] -> ()
  | (key', it) :: tl ->
    let (| ids, items |) = it in
    if key = f key'
    then begin
      seq_wf_tail ids;
      List.append_l_nil (items_to_values items y1);
      List.append_l_nil (items_to_values items y2);
      items_split items Set.empty y1 y2 [] []
    end
    else ls_fb_inj f tl fb fbf key y1 y2

and adb_inj (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (x1 x2: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
: Lemma
  (requires (
    wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') /\
    content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x1 ==
      content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x2))
  (ensures (x1 == x2))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'; 0])
= let clo (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Tot (list asn1_value) =
    let (| key, y |) = s in
    terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key y
  in
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x1 ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) -> (let (| key, y |) = s in terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key y) <: list asn1_value) x1))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x2 ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) -> (let (| key, y |) = s in terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key y) <: list asn1_value) x2))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  let tail (y: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Lemma (wf_tail idp Set.empty (clo y)) =
    let (| key, _ |) = y in
    terminal_to_value_id kid key_k key;
    any_prefix_wf_tail (Set.singleton kid) idp (clo y)
  in
  FStar.Classical.forall_intro tail;
  let inj (y1 y2: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Lemma (requires (clo y1 == clo y2)) (ensures (y1 == y2)) =
    let (| key1, z1 |) = y1 in
    let (| key2, z2 |) = y2 in
    terminal_inj kid key_k key1 key2;
    ls_inj (key_of_lit key_k) ls key1 z1 z2
  in
  FStar.Classical.forall_intro_2 (fun y1 y2 -> FStar.Classical.move_requires (inj y1) y2);
  items_any_split prefix Set.empty clo x1 x2

and adb_fb_inj (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (x1 x2: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
: Lemma
  (requires (
    wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') /\
    content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x1 ==
      content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x2))
  (ensures (x1 == x2))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'; 0])
= let fbf (z: asn1_sequence_t_core fbitems) : Tot (list asn1_value) = items_to_values fbitems z in
  let clo (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Tot (list asn1_value) =
    let (| key, y |) = s in
    terminal_to_value kid key_k key ::
    ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) key y
  in
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x1 ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) -> (let (| key, y |) = s in terminal_to_value kid key_k key :: ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) key y) <: list asn1_value) x1))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x2 ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) -> (let (| key, y |) = s in terminal_to_value kid key_k key :: ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) key y) <: list asn1_value) x2))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  fb_precedes idp prefix kid key_k ls fbids fbitems pf pf';
  let fbinj (z1 z2: asn1_sequence_t_core fbitems) : Lemma (requires (fbf z1 == fbf z2)) (ensures (z1 == z2)) =
    seq_wf_tail fbids;
    List.append_l_nil (items_to_values fbitems z1);
    List.append_l_nil (items_to_values fbitems z2);
    items_split fbitems Set.empty z1 z2 [] []
  in
  FStar.Classical.forall_intro_2 (fun z1 z2 -> FStar.Classical.move_requires (fbinj z1) z2);
  let tail (y: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Lemma (wf_tail idp Set.empty (clo y)) =
    let (| key, _ |) = y in
    terminal_to_value_id kid key_k key;
    any_prefix_wf_tail (Set.singleton kid) idp (clo y)
  in
  FStar.Classical.forall_intro tail;
  let inj (y1 y2: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Lemma (requires (clo y1 == clo y2)) (ensures (y1 == y2)) =
    let (| key1, z1 |) = y1 in
    let (| key2, z2 |) = y2 in
    terminal_inj kid key_k key1 key2;
    ls_fb_inj (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) fbf key1 z1 z2
  in
  FStar.Classical.forall_intro_2 (fun y1 y2 -> FStar.Classical.move_requires (inj y1) y2);
  items_any_split prefix Set.empty clo x1 x2
#pop-options

(* Consequences *)

(* A typed value is encodable iff its generic value conforms to the schema *)

let conforms_encodable (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma
  (requires (wf k /\ conforms k (to_value k x) == true))
  (ensures (encodable k x))
= let e = asn1_enc k x in
  parsed_spec_correct k e;
  match parse (asn1_as_parser k) e with
  | Some (x', n) ->
    Seq.lemma_eq_elim (Seq.slice e 0 n) e;
    asn1_value_enc_inj (to_value k x') (to_value k x);
    to_value_inj k x' x
  | None -> ()

let encodable_iff_conforms (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma
  (requires (wf k))
  (ensures (encodable k x <==> conforms k (to_value k x) == true))
= FStar.Classical.move_requires (encodable_conforms k) x;
  FStar.Classical.move_requires (conforms_encodable k) x

(* The serializer is injective on all values, encodable or not *)

let asn1_enc_inj (#s: _) (k: asn1_k s) (x1 x2: asn1_t k)
: Lemma
  (requires (wf k /\ asn1_enc k x1 == asn1_enc k x2))
  (ensures (x1 == x2))
= asn1_value_enc_inj (to_value k x1) (to_value k x2);
  to_value_inj k x1 x2
