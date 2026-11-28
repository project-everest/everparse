module ASN1.Spec.Raw.Value

(* Generic values of raw values (`ASN1.Spec.Raw`), and the characterization
   of `check_ser` by the typed parser.

   `rvalue k y` is the generic value (`ASN1.Spec.Value`) of a raw value `y`,
   following `ASN1.Spec.ToValue.to_value`: leaves are encoded with
   `raw_leaf_enc`, the components of a SET are sorted by tag, the elements
   of a SET OF are sorted by encoding, and a DEFAULT component explicitly
   set to its default value is omitted.

   For every well-formed schema `k`:
   - if `check_ser k u y == Some x`, then the generic encoding of
     `rvalue k y` is `asn1_enc k x` (`rvalue_check_ser`);
   - conversely, if the typed parser accepts exactly the generic encoding
     of `rvalue k y`, then `check_ser k u y` is the parsed value
     (`rvalue_parse`.)
   So a writer of the generic encoding of `rvalue k y` followed by the
   typed validator succeeds exactly when `check_ser k u y` is `Some _`. *)

open LowParse.Tot.Base
open ASN1.Bytes
open ASN1.Base
open ASN1.Spec.Value.Enc
open ASN1.Spec.Content.Enc
open ASN1.Spec.Interpreter
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue
open ASN1.Spec.Serializer
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot
module Set = FStar.Set
module Cast = FStar.Int.Cast
module LPC = LowParse.Spec.Combinators
module Inj = ASN1.Spec.ToValue.Inj
module TVS = ASN1.Spec.ToValue.Set
module Set_ = ASN1.Spec.Set
module IE = ASN1.Spec.IdentifierU32.Enc
module INT = ASN1.Spec.Content.INTEGER

(* Raw leaves: `raw_leaf_enc` agrees with `leaf_enc` only on forgotten
   typed leaves *)

let rec raw_byte_list_enc_inj (l1 l2: list U8.t)
: Lemma (requires (list_enc raw_byte_enc l1 == list_enc raw_byte_enc l2)) (ensures (l1 == l2)) (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    let e1 = list_enc raw_byte_enc l1 in
    assert (Seq.index e1 0 == a1);
    assert (Seq.index (list_enc raw_byte_enc l2) 0 == a2);
    Seq.lemma_eq_elim (Seq.slice e1 1 (Seq.length e1)) (list_enc raw_byte_enc q1);
    Seq.lemma_eq_elim (Seq.slice e1 1 (Seq.length e1)) (list_enc raw_byte_enc q2);
    raw_byte_list_enc_inj q1 q2
  | [], _ :: _ -> assert (Seq.length (list_enc raw_byte_enc l2) > 0)
  | _ :: _, [] -> assert (Seq.length (list_enc raw_byte_enc l1) > 0)

let enc_arc_first (v: U32.t)
: Lemma (Seq.length (enc_arc v) > 0 /\ Seq.index (enc_arc v) 0 <> 0x80uy)
= if U32.v v < 128
  then begin
    FStar.Math.Lemmas.small_mod (U32.v v) (pow2 8);
    assert (U8.v (Cast.uint32_to_uint8 v) == U32.v v)
  end else begin
    IE.id_digit_first v;
    if IE.id_bound v = 0
    then IE.id_digit_last v
    else ()
  end

let oid_enc_first (l: asn1_oid_t)
: Lemma (Seq.length (oid_enc l) > 0 /\ Seq.index (oid_enc l) 0 <> 0x80uy)
= enc_arc_first (oid_head l)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let raw_leaf_enc_mixed (k: leaf_k) (y: asn1_raw_terminal_t k) (x: asn1_terminal_t k)
: Lemma (requires (raw_leaf_enc k y == leaf_enc k x)) (ensures (y == forget_terminal k x))
= raw_leaf_enc_forget k x;
  match k with
  | ASN1_BOOLEAN ->
    assert (Seq.index (raw_leaf_enc k y) 0 == Seq.index (leaf_enc k x) 0)
  | ASN1_INTEGER bound -> ()
  | ASN1_BITSTRING ->
    let y' : (U8.t & asn1_bytes) = y in
    let x' : asn1_bitstring_t = x in
    let e = raw_leaf_enc k y in
    assert (Seq.index e 0 == fst y');
    assert (Seq.index e 0 == BYTES_WITH_UNUSEDBITS?.unused x');
    Seq.lemma_eq_elim (Seq.slice e 1 (Seq.length e)) (snd y');
    Seq.lemma_eq_elim (Seq.slice e 1 (Seq.length e)) (BYTES_WITH_UNUSEDBITS?.b x')
  | ASN1_PRINTABLESTRING
  | ASN1_IA5STRING
  | ASN1_VISIBLESTRING
  | ASN1_NUMERICSTRING ->
    raw_byte_list_enc_inj y (forget_terminal k x)
  | ASN1_NULL -> ()
  | ASN1_OID ->
    let y' : list U32.t = y in
    let x' : asn1_oid_t = x in
    if asn1_OID_wf y'
    then begin
      parse_oid_enc y';
      parse_oid_enc x'
    end else
      oid_enc_first x'
  | ASN1_RELATIVE_OID ->
    let y' : list U32.t = y in
    let x' : list U32.t = x in
    parse_arcs_enc y';
    parse_arcs_enc x'
  | _ -> ()
#pop-options

(* Generic values of raw values *)

let rec rterm (id: asn1_id_t) (k: asn1_terminal_k) (y: asn1_raw_terminal_t k) : Tot asn1_value (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_raw_terminal_t k2);
    mk_encap id (rterm id2 k2 (coerce_eq #(asn1_raw_terminal_t k) #(asn1_raw_terminal_t k2) () y))
  | _ -> mk_prim id (raw_leaf_enc k y)

let rec rterm_forget (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k)
: Lemma (ensures (rterm id k (forget_terminal k x) == terminal_to_value id k x)) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_t k2);
    rterm_forget id2 k2 (coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k2) () x)
  | _ -> raw_leaf_enc_forget k x

let rec rterm_mixed (id: asn1_id_t) (k: asn1_terminal_k) (y: asn1_raw_terminal_t k) (x: asn1_terminal_t k)
: Lemma (requires (rterm id k y == terminal_to_value id k x)) (ensures (y == forget_terminal k x)) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_t k2);
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_raw_terminal_t k2);
    let y' : asn1_raw_terminal_t k2 = coerce_eq #(asn1_raw_terminal_t k) #(asn1_raw_terminal_t k2) () y in
    let x' : asn1_terminal_t k2 = coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k2) () x in
    Inj.mk_encap_inj id (rterm id2 k2 y') (terminal_to_value id2 k2 x');
    rterm_mixed id2 k2 y' x'
  | _ -> raw_leaf_enc_mixed k y x

let rterm_id (id: asn1_id_t) (k: asn1_terminal_k) (y: asn1_raw_terminal_t k)
: Lemma (value_id (rterm id k y) == any_id id)
= ()

(* SET OF elements are sorted by their generic encodings *)

let vsort (l: list asn1_value) : Tot (list asn1_value) = sort_enc asn1_value_enc l

let rec rcontent (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k) : Tot asn1_value (decreases %[k; 0]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> rterm id k' y
  | ASN1_TERMINAL k' -> rterm id k' y
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    mk_cons id (ritems items y)
  | ASN1_SET _ items _ -> mk_cons id (sort_by_tag (ritems items y))
  | ASN1_SEQUENCE_OF _ k' -> mk_cons id (rlist k' y)
  | ASN1_SET_OF _ k' -> mk_cons id (vsort (rlist k' y))
  | ASN1_PREFIXED k' -> mk_encap id (rvalue k' y)
  | ASN1_ANY_DEFINED_BY _ prefix kid key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let sfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key :: rls key_k ls key y
      in
      mk_cons id (ritems_any prefix sfx y)
    | Some fb ->
      let (| _, fbitems |) = fb in
      let sfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key ::
        rls_fb key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> ritems fbitems z) key y
      in
      mk_cons id (ritems_any prefix sfx y)
    end

and rlist (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) : Tot (list asn1_value) (decreases %[k; l]) =
  match l with
  | [] -> []
  | a :: q -> rvalue k a :: rlist k q

and rvalue (#s: _) (k: asn1_k s) (y: asn1_raw_t k) : Tot asn1_value (decreases %[k; y]) =
  match k with
  | ASN1_ILC id k' -> rcontent id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    rchoice lc id z
  | ASN1_ANY_ILC -> y

and rchoice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc)) : Tot asn1_value (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then rcontent id c y
    else rchoice tl id y

and rls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_raw_terminal_t key_k) (y: idlookup_t key (raw_any_t_core key_k ls)) : Tot (list asn1_value) (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then ritems items y
    else rls key_k tl key y

and rls_fb (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: Type) (fbf: fb -> Tot (list asn1_value)) (key: asn1_raw_terminal_t key_k) (y: idlookup_with_fallback_t key (raw_any_t_core key_k ls) fb) : Tot (list asn1_value) (decreases %[ls; 0]) =
  match ls with
  | [] -> fbf y
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then ritems items y
    else rls_fb key_k tl fb fbf key y

and rdec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk) : Tot (list asn1_value) (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> [rvalue k y]
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> [] | Some z -> [rvalue k z])
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with
     | None -> []
     | Some z -> if z = raw_key_of_lit k defv_l then [] else [rterm id k z])
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with
     | None -> []
     | Some z -> if z = raw_key_of_lit k defv_l then [] else [rterm id k z])

and ritems (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items) : Tot (list asn1_value) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> rdec dk y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, b) = y' in
    rdec dk a `List.append` ritems tl b

and ritems_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t) : Tot (list asn1_value) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfx y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, b) = y' in
    rdec dk a `List.append` sfx b
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, b) = y' in
    rdec dk a `List.append` ritems_any tl sfx b

(* Lexicographic order of byte sequences *)

let lex_unfold (a b: bytes)
: Lemma (Set_.lex_byte_order a b == (
    if Seq.length a = 0 then true
    else if Seq.length b = 0 then false
    else if Seq.index a 0 `U8.lt` Seq.index b 0 then true
    else if Seq.index b 0 `U8.lt` Seq.index a 0 then false
    else Set_.lex_byte_order (Seq.slice a 1 (Seq.length a)) (Seq.slice b 1 (Seq.length b))))
= assert_norm (Set_.lex_byte_order a b == Set_.lex_byte_order' (Seq.length a) a (Seq.length b) b)

let rec lex_total (a b: bytes)
: Lemma (ensures (Set_.lex_byte_order a b \/ Set_.lex_byte_order b a)) (decreases (Seq.length a))
= lex_unfold a b;
  lex_unfold b a;
  if Seq.length a = 0 || Seq.length b = 0 then ()
  else lex_total (Seq.slice a 1 (Seq.length a)) (Seq.slice b 1 (Seq.length b))

#push-options "--fuel 0 --ifuel 0"
let rec lex_trans (a b c: bytes)
: Lemma (requires (Set_.lex_byte_order a b /\ Set_.lex_byte_order b c)) (ensures (Set_.lex_byte_order a c)) (decreases (Seq.length a))
= lex_unfold a b;
  lex_unfold b c;
  lex_unfold a c;
  if Seq.length a = 0 || Seq.length b = 0 || Seq.length c = 0 then ()
  else if Seq.index a 0 = Seq.index b 0 && Seq.index b 0 = Seq.index c 0
  then lex_trans (Seq.slice a 1 (Seq.length a)) (Seq.slice b 1 (Seq.length b)) (Seq.slice c 1 (Seq.length c))
  else ()
#pop-options

let rec lex_antisym (a b: bytes)
: Lemma (requires (Set_.lex_byte_order a b /\ Set_.lex_byte_order b a)) (ensures (a == b)) (decreases (Seq.length a))
= lex_unfold a b;
  lex_unfold b a;
  if Seq.length a = 0 || Seq.length b = 0 then Seq.lemma_eq_elim a b
  else begin
    let a' = Seq.slice a 1 (Seq.length a) in
    let b' = Seq.slice b 1 (Seq.length b) in
    lex_antisym a' b';
    Seq.lemma_eq_elim a (Seq.cons (Seq.index a 0) a');
    Seq.lemma_eq_elim b (Seq.cons (Seq.index b 0) b')
  end

(* Insertion sorts *)

let lex_enc (#t: Type) (enc: t -> Tot asn1_bytes) (a b: t) : Tot bool = Set_.lex_byte_order (enc a) (enc b)

let rec insert_comm (#t: Type) (enc: t -> Tot asn1_bytes) (a b: t) (l: list t)
: Lemma
  (requires (lex_enc enc a b /\ (forall (x y: t) . enc x == enc y ==> x == y)))
  (ensures (insert_enc enc a (insert_enc enc b l) == insert_enc enc b (insert_enc enc a l)))
  (decreases l)
= if lex_enc enc b a then lex_antisym (enc a) (enc b);
  match l with
  | [] -> ()
  | h :: q ->
    if lex_enc enc a h then ()
    else begin
      FStar.Classical.move_requires (lex_trans (enc a) (enc b)) (enc h);
      insert_comm enc a b q
    end

(* Inserting the elements of a list one by one, first to last *)
let rec sort_fold (#t: Type) (enc: t -> Tot asn1_bytes) (acc: list t) (l: list t) : Tot (list t) (decreases l) =
  match l with
  | [] -> acc
  | a :: q -> sort_fold enc (insert_enc enc a acc) q

let rec sort_fold_insert (#t: Type) (enc: t -> Tot asn1_bytes) (a: t) (acc: list t) (l: list t)
: Lemma
  (requires (forall (x y: t) . enc x == enc y ==> x == y))
  (ensures (sort_fold enc (insert_enc enc a acc) l == insert_enc enc a (sort_fold enc acc l)))
  (decreases l)
= match l with
  | [] -> ()
  | b :: q ->
    lex_total (enc a) (enc b);
    if lex_enc enc a b
    then insert_comm enc a b acc
    else insert_comm enc b a acc;
    sort_fold_insert enc a (insert_enc enc b acc) q

let rec sort_fold_eq (#t: Type) (enc: t -> Tot asn1_bytes) (l: list t)
: Lemma
  (requires (forall (x y: t) . enc x == enc y ==> x == y))
  (ensures (sort_fold enc [] l == sort_enc enc l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    sort_fold_insert enc a [] q;
    sort_fold_eq enc q

let rec map_insert (#t1 #t2: Type) (f: t1 -> Tot t2) (enc1: t1 -> Tot asn1_bytes) (enc2: t2 -> Tot asn1_bytes) (a: t1) (l: list t1)
: Lemma
  (requires (forall (x: t1) . enc1 x == enc2 (f x)))
  (ensures (List.map f (insert_enc enc1 a l) == insert_enc enc2 (f a) (List.map f l)))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> map_insert f enc1 enc2 a q

let rec map_sort (#t1 #t2: Type) (f: t1 -> Tot t2) (enc1: t1 -> Tot asn1_bytes) (enc2: t2 -> Tot asn1_bytes) (l: list t1)
: Lemma
  (requires (forall (x: t1) . enc1 x == enc2 (f x)))
  (ensures (List.map f (sort_enc enc1 l) == sort_enc enc2 (List.map f l)))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    map_sort f enc1 enc2 q;
    map_insert f enc1 enc2 a (sort_enc enc1 q)

let rec insert_length (#t: Type) (enc: t -> Tot asn1_bytes) (a: t) (l: list t)
: Lemma (ensures (List.length (insert_enc enc a l) == List.length l + 1)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> insert_length enc a q

let rec sort_length (#t: Type) (enc: t -> Tot asn1_bytes) (l: list t)
: Lemma (ensures (List.length (sort_enc enc l) == List.length l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> sort_length enc q; insert_length enc a (sort_enc enc q)

let rec insert_memP (#t: Type) (enc: t -> Tot asn1_bytes) (a: t) (l: list t) (v: t)
: Lemma (ensures (List.memP v (insert_enc enc a l) <==> (v == a \/ List.memP v l))) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> insert_memP enc a q v

let rec sort_memP (#t: Type) (enc: t -> Tot asn1_bytes) (l: list t) (v: t)
: Lemma (ensures (List.memP v (sort_enc enc l) <==> List.memP v l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> sort_memP enc q v; insert_memP enc a (sort_enc enc q) v

let rec list_to_values_map (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (ensures (list_to_values k l == List.map (to_value k) l)) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_to_values_map k q

let list_to_values_sort (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (list_to_values k (sort_enc (asn1_enc k) l) == vsort (list_to_values k l))
= list_to_values_map k l;
  list_to_values_map k (sort_enc (asn1_enc k) l);
  map_sort (to_value k) (asn1_enc k) asn1_value_enc l

let rec list_to_values_memP (#s: _) (k: asn1_k s) (l: list (asn1_t k)) (v: asn1_value)
: Lemma
  (requires (List.memP v (list_to_values k l)))
  (ensures (exists (x: asn1_t k) . to_value k x == v))
  (decreases l)
= match l with
  | a :: q ->
    FStar.Classical.move_requires (list_to_values_memP k q) v;
    assert (to_value k a == v ==> (exists (x: asn1_t k) . to_value k x == v))

(* R1: checked raw values have the generic value of their typed value *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec r1_value (#s: _) (k: asn1_k s) (y: asn1_raw_t k) (x: asn1_t k)
: Lemma (requires (check k y == Some x)) (ensures (rvalue k y == to_value k x)) (decreases %[k; 2])
= match k with
  | ASN1_ILC id k' -> r1_content id k' y x
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    begin match check_choice lc id z with
    | Some z' -> r1_choice lc id z z'
    | None -> ()
    end
  | ASN1_ANY_ILC -> ()

and r1_content (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k) (x: asn1_content_t k)
: Lemma (requires (check_content k y == Some x)) (ensures (rcontent id k y == content_to_value id k x)) (decreases %[k; 3])
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ ->
    forget_check_terminal k' y;
    let Some v = check_terminal k' y in
    rterm_forget id k' v
  | ASN1_TERMINAL k' ->
    forget_check_terminal k' y;
    rterm_forget id k' x
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    r1_items items y x
  | ASN1_SET _ items _ -> r1_items items y x
  | ASN1_SEQUENCE_OF _ k' ->
    let Some l = check_list k' y in
    r1_list k' y l
  | ASN1_SET_OF _ k' ->
    let Some l = check_list k' y in
    r1_list k' y l;
    list_to_values_sort k' l
  | ASN1_PREFIXED k' -> r1_value k' y x
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None -> r1_adb id idp prefix kid key_k ls pf pf' y x
    | Some fb ->
      let (| fbids, fbitems |) = fb in
      r1_adb_fb id idp prefix kid key_k ls fbids fbitems pf pf' y x
    end

and r1_adb (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
  (x: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
: Lemma
  (requires (check_content (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == Some x))
  (ensures (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'; 2])
= let rclo (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key :: rls key_k ls key z
  in
  let tclo (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key z
  in
  assert (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y ==
    mk_cons id (ritems_any prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, z |) = s in rterm kid key_k key :: rls key_k ls key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%rcontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) -> (let (| key, z |) = s in terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key z) <: list asn1_value) x))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  let rs = raw_items_any_sfx prefix #(make_gen_choice_type (raw_any_t_core key_k ls)) y in
  let Some s = check_adb_sfx key_k ls rs in
  let (| rkey, ry |) = rs in
  forget_check_terminal key_k rkey;
  let Some key = check_terminal key_k rkey in
  let Some z = check_ls key_k ls key ry in
  r1_ls key_k ls key ry z;
  rterm_forget kid key_k key;
  assert (rclo rs == tclo s);
  r1_items_any prefix tclo rclo y s x

and r1_adb_fb (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
  (x: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
: Lemma
  (requires (check_content (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == Some x))
  (ensures (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'; 2])
= let k0 = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf' in
  fb_precedes k0;
  let rclo (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key ::
    rls_fb key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> ritems fbitems w) key z
  in
  let tclo (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    terminal_to_value kid key_k key ::
    ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (w: asn1_sequence_t_core fbitems) -> items_to_values fbitems w) key z
  in
  assert (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y ==
    mk_cons id (ritems_any prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, z |) = s in rterm kid key_k key :: rls_fb key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> ritems fbitems w) key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%rcontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) -> (let (| key, z |) = s in terminal_to_value kid key_k key :: ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (w: asn1_sequence_t_core fbitems) -> items_to_values fbitems w) key z) <: list asn1_value) x))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  let rs = raw_items_any_sfx prefix #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) y in
  let Some s = check_adb_fb_sfx k0 key_k ls fbitems rs in
  let (| rkey, ry |) = rs in
  forget_check_terminal key_k rkey;
  let Some key = check_terminal key_k rkey in
  let Some z = check_ls_fb k0 key_k ls fbitems key ry in
  r1_ls_fb k0 key_k ls fbitems key ry z;
  rterm_forget kid key_k key;
  assert (rclo rs == tclo s);
  r1_items_any prefix tclo rclo y s x

and r1_list (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) (x: list (asn1_t k))
: Lemma (requires (check_list k l == Some x)) (ensures (rlist k l == list_to_values k x)) (decreases %[k; 3; l])
= match l with
  | [] -> ()
  | a :: q ->
    let Some a' = check k a in
    let Some q' = check_list k q in
    r1_value k a a';
    r1_list k q q'

and r1_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc)) (x: idlookup_t id (asn1_lc_t lc))
: Lemma (requires (check_choice lc id y == Some x)) (ensures (rchoice lc id y == choice_to_value lc id x)) (decreases %[lc; 0])
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then r1_content id c y x
    else r1_choice tl id y x

and r1_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y: idlookup_t (forget_terminal key_k key) (raw_any_t_core key_k ls)) (x: idlookup_t key (typed_any_t key_k ls))
: Lemma (requires (check_ls key_k ls key y == Some x)) (ensures (rls key_k ls (forget_terminal key_k key) y == ls_to_values (key_of_lit key_k) ls key x)) (decreases %[ls; 0])
= match ls with
  | [] -> false_elim ()
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then r1_items items y x
    else begin
      forget_key_ne key_k key l;
      r1_ls key_k tl key y x
    end

and r1_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y: idlookup_with_fallback_t (forget_terminal key_k key) (raw_any_t_core key_k ls) (raw_items_t fbitems)) (x: idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))
: Lemma
  (requires (check_ls_fb k0 key_k ls fbitems key y == Some x))
  (ensures (rls_fb key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> ritems fbitems w) (forget_terminal key_k key) y ==
    ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (w: asn1_sequence_t_core fbitems) -> items_to_values fbitems w) key x))
  (decreases %[k0; 1; ls])
= match ls with
  | [] -> r1_items fbitems y x
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then r1_items items y x
    else begin
      forget_key_ne key_k key l;
      r1_ls_fb k0 key_k tl fbitems key y x
    end

and r1_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk) (x: asn1_decorated_t_core dk)
: Lemma (requires (check_dec dk y == Some x)) (ensures (rdec dk y == dec_to_values dk x)) (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> r1_value k y x
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    begin match y' with
    | None -> ()
    | Some z -> let Some z' = check k z in r1_value k z z'
    end
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    begin match y' with
    | None -> ()
    | Some z ->
      forget_check_terminal k z;
      let Some v = check_terminal k z in
      if v = key_of_lit k defv_l then ()
      else begin
        forget_key_ne k v defv_l;
        rterm_forget id k v
      end
    end
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    begin match y' with
    | None -> ()
    | Some z ->
      forget_check_terminal k z;
      let Some v = check_terminal k z in
      if v = key_of_lit k defv_l then ()
      else begin
        forget_key_ne k v defv_l;
        rterm_forget id k v
      end
    end

and r1_items (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items) (x: asn1_sequence_t_core items)
: Lemma (requires (check_items items y == Some x)) (ensures (ritems items y == items_to_values items x)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> r1_dec dk y x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, b) = y' in
    let Some a' = check_dec dk a in
    let Some b' = check_items tl b in
    r1_dec dk a a';
    r1_items tl b b'

and r1_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t #rsfx_t: Type) (tsfx: sfx_t -> Tot (list asn1_value)) (rsfx: rsfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items rsfx_t) (s: sfx_t) (x: asn1_sequence_any_t_core items sfx_t)
: Lemma
  (requires (check_items_any items #sfx_t #rsfx_t y s == Some x /\ rsfx (raw_items_any_sfx items y) == tsfx s))
  (ensures (ritems_any items rsfx y == items_any_to_values items tsfx x))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & rsfx_t = y in
    let (a, _) = y' in
    let Some a' = check_dec dk a in
    r1_dec dk a a'
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl rsfx_t = y in
    let (a, b) = y' in
    let Some a' = check_dec dk a in
    let Some b' = check_items_any tl #sfx_t #rsfx_t b s in
    r1_dec dk a a';
    r1_items_any tl tsfx rsfx b s b'
#pop-options

(* Identifiers of generic values of raw values *)

let rcontent_id (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k)
: Lemma (value_id (rcontent id k y) == any_id id)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> rterm_id id k' y
  | ASN1_TERMINAL k' -> rterm_id id k' y
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ ofb _ _ ->
    begin match ofb with
    | None -> ()
    | Some _ -> ()
    end
  | _ -> ()

let rec rchoice_id (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc))
: Lemma
  (ensures (
    value_id (rchoice lc id y) == any_id id /\
    List.mem id (List.map fst lc) /\
    (wf_lc lc ==> asn1_any_id_valid id)))
  (decreases lc)
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then rcontent_id id c y
    else rchoice_id tl id y

let rvalue_mem (#s: _) (k: asn1_k s) (y: asn1_raw_t k)
: Lemma
  (requires (wf k))
  (ensures (Set.mem (value_id (rvalue k y)) s))
= match k with
  | ASN1_ILC id k' -> rcontent_id id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    rchoice_id lc id z;
    Inj.mem_as_set' id (List.map fst lc)
  | ASN1_ANY_ILC -> ()

let rdec_values (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk)
: Lemma
  (requires (wf_dec dk))
  (ensures (Inj.dec_values_ok s d (rdec dk y)))
= match dk with
  | ASN1_PLAIN_ILC k -> rvalue_mem k y
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> () | Some z -> rvalue_mem k z)
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> () | Some z -> rterm_id id k z)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> () | Some z -> rterm_id id k z)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec ritems_head (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (y: raw_items_t items) (r: list asn1_value)
: Lemma
  (requires (wf_items items /\ Inj.wf_tail ids s r))
  (ensures (Inj.head_not_in (ritems items y `List.append` r) s))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    rdec_values dk y;
    Inj.dec_head_not_in s s' d (rdec dk y) r
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, b) = y' in
    rdec_values dk a;
    List.append_assoc (rdec dk a) (ritems tl b) r;
    if Nil? (rdec dk a) then ritems_head tl (Set.union s s') b r;
    Inj.dec_head_not_in s s' d (rdec dk a) (ritems tl b `List.append` r)

let rec ritems_any_head (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t)
: Lemma
  (requires (wf_items items /\ (forall (z: sfx_t) . Inj.wf_tail ids s (sfx z))))
  (ensures (Inj.head_not_in (ritems_any items sfx y) s))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, b) = y' in
    rdec_values dk a;
    Inj.dec_head_not_in s s' d (rdec dk a) (sfx b)
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, b) = y' in
    assert (Inj.wf_tail ids s (sfx (raw_items_any_sfx tl b)));
    rdec_values dk a;
    if Nil? (rdec dk a) then ritems_any_head tl (Set.union s s') sfx b;
    Inj.dec_head_not_in s s' d (rdec dk a) (ritems_any tl sfx b)

let rec rset_items_not_in (#ids: _) (items: asn1_gen_items_l ids) (s0: Set.set asn1_id_t) (y: raw_items_t items)
: Lemma
  (requires (wf_items items /\ asn1_set_k_wf' s0 ids))
  (ensures (forall v . List.memP v (ritems items y) ==> ~ (Set.mem (value_id v) s0)))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    rdec_values dk y;
    assert (forall (i: asn1_id_t) . asn1_same_tag i i)
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, b) = y' in
    rdec_values dk a;
    rset_items_not_in tl s0 b;
    assert (forall (i: asn1_id_t) . asn1_same_tag i i);
    FStar.Classical.forall_intro (List.append_memP (rdec dk a) (ritems tl b))
#pop-options

(* M: a raw value with the generic value of a typed value checks to it *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec m_value (#s: _) (k: asn1_k s) (y: asn1_raw_t k) (x: asn1_t k)
: Lemma
  (requires (wf k /\ rvalue k y == to_value k x))
  (ensures (check k y == Some x))
  (decreases %[k; 2])
= match k with
  | ASN1_ILC id k' -> m_content id k' y x
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, z |) = y' in
    let (| id2, z2 |) = x' in
    rchoice_id lc id z;
    Inj.choice_to_value_id lc id2 z2;
    m_choice lc id z z2
  | ASN1_ANY_ILC -> ()

and m_content (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k) (x: asn1_content_t k)
: Lemma
  (requires (wf_content id k /\ rcontent id k y == content_to_value id k x))
  (ensures (check_content k y == Some x))
  (decreases %[k; 3])
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ ->
    rterm_mixed id k' y x;
    check_forget_terminal k' x
  | ASN1_TERMINAL k' ->
    rterm_mixed id k' y x;
    check_forget_terminal k' x
  | ASN1_SEQUENCE gitems ->
    let (| ids, items |) = gitems in
    Inj.seq_wf_tail ids;
    List.append_l_nil (ritems items y);
    List.append_l_nil (items_to_values items x);
    m_items_split items Set.empty y x [] []
  | ASN1_SET ids items _ ->
    let l1 = ritems items y in
    let l2 = items_to_values items x in
    let prf (v: asn1_value) : Lemma (TVS.count v l1 == TVS.count v l2) =
      TVS.count_sort l1 v;
      TVS.count_sort l2 v
    in
    FStar.Classical.forall_intro prf;
    m_set items y x
  | ASN1_SEQUENCE_OF _ k' ->
    let lx : list (asn1_t k') = x in
    m_list k' y lx;
    let Some l = check_list k' y in
    r1_list k' y l;
    Inj.list_inj k' l lx
  | ASN1_SET_OF _ k' ->
    let lx : list (asn1_t k') = x in
    FStar.Classical.forall_intro (sort_memP asn1_value_enc (rlist k' y));
    m_list k' y lx;
    let Some l = check_list k' y in
    r1_list k' y l;
    list_to_values_sort k' l;
    Inj.list_inj k' (sort_enc (asn1_enc k') l) lx
  | ASN1_PREFIXED k' ->
    Inj.mk_encap_inj id (rvalue k' y) (to_value k' x);
    m_value k' y x
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None -> m_adb id idp prefix kid key_k ls pf pf' y x
    | Some fb ->
      let (| fbids, fbitems |) = fb in
      m_adb_fb id idp prefix kid key_k ls fbids fbitems pf pf' y x
    end

and m_adb (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
  (x: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
: Lemma
  (requires (
    wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') /\
    rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x))
  (ensures (check_content (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == Some x))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'; 2])
= let rclo (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key :: rls key_k ls key z
  in
  let tclo (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key z
  in
  assert (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y ==
    mk_cons id (ritems_any prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, z |) = s in rterm kid key_k key :: rls key_k ls key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%rcontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') x ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) -> (let (| key, z |) = s in terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key z) <: list asn1_value) x))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  let ttail (z: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Lemma (Inj.wf_tail idp Set.empty (tclo z)) =
    let (| key, _ |) = z in
    Inj.terminal_to_value_id kid key_k key;
    Inj.any_prefix_wf_tail (Set.singleton kid) idp (tclo z)
  in
  FStar.Classical.forall_intro ttail;
  let rtail (z: make_gen_choice_type (raw_any_t_core key_k ls)) : Lemma (Inj.wf_tail idp Set.empty (rclo z)) =
    let (| key, _ |) = z in
    rterm_id kid key_k key;
    Inj.any_prefix_wf_tail (Set.singleton kid) idp (rclo z)
  in
  FStar.Classical.forall_intro rtail;
  m_items_any_split prefix Set.empty tclo rclo y x;
  let rs = raw_items_any_sfx prefix #(make_gen_choice_type (raw_any_t_core key_k ls)) y in
  let ts = Inj.any_sfx prefix #(make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) x in
  let (| rkey, ry |) = rs in
  let (| key, z |) = ts in
  rterm_mixed kid key_k rkey key;
  check_forget_terminal key_k key;
  m_ls key_k ls key ry z

and m_adb_fb (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
  (x: asn1_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
: Lemma
  (requires (
    wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') /\
    rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x))
  (ensures (check_content (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == Some x))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'; 2])
= let k0 = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf' in
  fb_precedes k0;
  let rclo (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key ::
    rls_fb key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> ritems fbitems w) key z
  in
  let tclo (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    terminal_to_value kid key_k key ::
    ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (w: asn1_sequence_t_core fbitems) -> items_to_values fbitems w) key z
  in
  assert (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y ==
    mk_cons id (ritems_any prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, z |) = s in rterm kid key_k key :: rls_fb key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> ritems fbitems w) key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%rcontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (content_to_value id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') x ==
    mk_cons id (items_any_to_values prefix (fun (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) -> (let (| key, z |) = s in terminal_to_value kid key_k key :: ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (w: asn1_sequence_t_core fbitems) -> items_to_values fbitems w) key z) <: list asn1_value) x))
    by (FStar.Tactics.norm [delta_only [`%content_to_value]; zeta; iota]; FStar.Tactics.trefl ());
  let ttail (z: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Lemma (Inj.wf_tail idp Set.empty (tclo z)) =
    let (| key, _ |) = z in
    Inj.terminal_to_value_id kid key_k key;
    Inj.any_prefix_wf_tail (Set.singleton kid) idp (tclo z)
  in
  FStar.Classical.forall_intro ttail;
  let rtail (z: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Lemma (Inj.wf_tail idp Set.empty (rclo z)) =
    let (| key, _ |) = z in
    rterm_id kid key_k key;
    Inj.any_prefix_wf_tail (Set.singleton kid) idp (rclo z)
  in
  FStar.Classical.forall_intro rtail;
  m_items_any_split prefix Set.empty tclo rclo y x;
  let rs = raw_items_any_sfx prefix #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) y in
  let ts = Inj.any_sfx prefix #(make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) x in
  let (| rkey, ry |) = rs in
  let (| key, z |) = ts in
  rterm_mixed kid key_k rkey key;
  check_forget_terminal key_k key;
  m_ls_fb k0 key_k ls fbitems key ry z

and m_list (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) (lx: list (asn1_t k))
: Lemma
  (requires (wf k /\ (forall v . List.memP v (rlist k l) ==> List.memP v (list_to_values k lx))))
  (ensures (Some? (check_list k l)))
  (decreases %[k; 3; l])
= match l with
  | [] -> ()
  | a :: q ->
    assert (List.memP (rvalue k a) (rlist k l));
    list_to_values_memP k lx (rvalue k a);
    let xa = FStar.IndefiniteDescription.indefinite_description_ghost (asn1_t k) (fun xa -> to_value k xa == rvalue k a) in
    m_value k a xa;
    m_list k q lx

and m_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc)) (x: idlookup_t id (asn1_lc_t lc))
: Lemma
  (requires (wf_lc lc /\ rchoice lc id y == choice_to_value lc id x))
  (ensures (check_choice lc id y == Some x))
  (decreases %[lc; 0])
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then m_content id c y x
    else m_choice tl id y x

and m_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y: idlookup_t (forget_terminal key_k key) (raw_any_t_core key_k ls)) (x: idlookup_t key (typed_any_t key_k ls))
: Lemma
  (requires (wf_ls ls /\ rls key_k ls (forget_terminal key_k key) y == ls_to_values (key_of_lit key_k) ls key x))
  (ensures (check_ls key_k ls key y == Some x))
  (decreases %[ls; 0])
= match ls with
  | [] -> false_elim ()
  | (l, it) :: tl ->
    let (| ids, items |) = it in
    if key = key_of_lit key_k l
    then begin
      Inj.seq_wf_tail ids;
      List.append_l_nil (ritems items y);
      List.append_l_nil (items_to_values items x);
      m_items_split items Set.empty y x [] []
    end
    else begin
      forget_key_ne key_k key l;
      m_ls key_k tl key y x
    end

and m_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y: idlookup_with_fallback_t (forget_terminal key_k key) (raw_any_t_core key_k ls) (raw_items_t fbitems)) (x: idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))
: Lemma
  (requires (
    wf_ls ls /\ wf_items fbitems /\ asn1_sequence_k_wf fbids /\
    rls_fb key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> ritems fbitems w) (forget_terminal key_k key) y ==
    ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (w: asn1_sequence_t_core fbitems) -> items_to_values fbitems w) key x))
  (ensures (check_ls_fb k0 key_k ls fbitems key y == Some x))
  (decreases %[k0; 1; ls])
= match ls with
  | [] ->
    Inj.seq_wf_tail fbids;
    List.append_l_nil (ritems fbitems y);
    List.append_l_nil (items_to_values fbitems x);
    m_items_split fbitems Set.empty y x [] []
  | (l, it) :: tl ->
    let (| ids, items |) = it in
    if key = key_of_lit key_k l
    then begin
      Inj.seq_wf_tail ids;
      List.append_l_nil (ritems items y);
      List.append_l_nil (items_to_values items x);
      m_items_split items Set.empty y x [] []
    end
    else begin
      forget_key_ne key_k key l;
      m_ls_fb k0 key_k tl fbitems key y x
    end

and m_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk) (x: asn1_decorated_t_core dk)
: Lemma
  (requires (wf_dec dk /\ rdec dk y == dec_to_values dk x))
  (ensures (check_dec dk y == Some x))
  (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> m_value k y x
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    let x' : option (asn1_t k) = x in
    (match y', x' with
     | Some z, Some z' -> m_value k z z'
     | _ -> ())
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let defv = key_of_lit k defv_l in
    let y' : option (asn1_raw_terminal_t k) = y in
    let x' : default_tv defv = x in
    begin match y' with
    | None -> ()
    | Some z ->
      if z = raw_key_of_lit k defv_l
      then check_forget_terminal k defv
      else begin match x' with
        | Nondefault v -> rterm_mixed id k z v; check_forget_terminal k v
        | Default -> ()
      end
    end
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let defv : LPC.parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let y' : option (asn1_raw_terminal_t k) = y in
    let x' : default_tv #(LPC.parse_filter_refine (restriction_pred r)) defv = x in
    begin match y' with
    | None -> ()
    | Some z ->
      if z = raw_key_of_lit k defv_l
      then check_forget_terminal k defv
      else begin match x' with
        | Nondefault v -> rterm_mixed id k z v; check_forget_terminal k v
        | Default -> ()
      end
    end

and m_items_split (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (y: raw_items_t items) (x: asn1_sequence_t_core items) (r1 r2: list asn1_value)
: Lemma
  (requires (
    wf_items items /\ Inj.wf_tail ids s r1 /\ Inj.wf_tail ids s r2 /\
    ritems items y `List.append` r1 == items_to_values items x `List.append` r2))
  (ensures (check_items items y == Some x /\ r1 == r2))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    rdec_values dk y;
    Inj.dec_values dk x;
    Inj.split_dec s s' d (rdec dk y) (dec_to_values dk x) r1 r2;
    m_dec dk y x
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a1, b1) = y' in
    let (a2, b2) = x' in
    rdec_values dk a1;
    Inj.dec_values dk a2;
    List.append_assoc (rdec dk a1) (ritems tl b1) r1;
    List.append_assoc (dec_to_values dk a2) (items_to_values tl b2) r2;
    if not (PLAIN? d) then begin
      ritems_head tl (Set.union s s') b1 r1;
      Inj.items_head tl (Set.union s s') b2 r2
    end;
    Inj.split_dec s s' d (rdec dk a1) (dec_to_values dk a2) (ritems tl b1 `List.append` r1) (items_to_values tl b2 `List.append` r2);
    m_dec dk a1 a2;
    let s1 : Set.set asn1_id_t = if PLAIN? d then Set.empty else Set.union s s' in
    m_items_split tl s1 b1 b2 r1 r2

and m_items_any_split (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (#sfx_t #rsfx_t: Type) (tsfx: sfx_t -> Tot (list asn1_value)) (rsfx: rsfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items rsfx_t) (x: asn1_sequence_any_t_core items sfx_t)
: Lemma
  (requires (
    wf_items items /\
    (forall (z: sfx_t) . Inj.wf_tail ids s (tsfx z)) /\
    (forall (z: rsfx_t) . Inj.wf_tail ids s (rsfx z)) /\
    ritems_any items rsfx y == items_any_to_values items tsfx x))
  (ensures (
    rsfx (raw_items_any_sfx items y) == tsfx (Inj.any_sfx items x) /\
    check_items_any items #sfx_t #rsfx_t y (Inj.any_sfx items x) == Some x))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & rsfx_t = y in
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    let (a1, b1) = y' in
    let (a2, b2) = x' in
    rdec_values dk a1;
    Inj.dec_values dk a2;
    assert (Inj.wf_tail ids s (rsfx b1));
    assert (Inj.wf_tail ids s (tsfx b2));
    Inj.split_dec s s' d (rdec dk a1) (dec_to_values dk a2) (rsfx b1) (tsfx b2);
    m_dec dk a1 a2
  | ASN1_GEN_ITEMS_CONS s' d dk tids tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl rsfx_t = y in
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    let (a1, b1) = y' in
    let (a2, b2) = x' in
    assert (Inj.wf_tail ids s (rsfx (raw_items_any_sfx tl b1)));
    assert (Inj.wf_tail ids s (tsfx (Inj.any_sfx tl b2)));
    rdec_values dk a1;
    Inj.dec_values dk a2;
    let s1 : Set.set asn1_id_t = if PLAIN? d then Set.empty else Set.union s s' in
    assert (forall (z: sfx_t) . Inj.wf_tail tids s1 (tsfx z));
    assert (forall (z: rsfx_t) . Inj.wf_tail tids s1 (rsfx z));
    if not (PLAIN? d) then begin
      ritems_any_head tl (Set.union s s') rsfx b1;
      Inj.items_any_head tl (Set.union s s') tsfx b2
    end;
    Inj.split_dec s s' d (rdec dk a1) (dec_to_values dk a2) (ritems_any tl rsfx b1) (items_any_to_values tl tsfx b2);
    m_dec dk a1 a2;
    m_items_any_split tl s1 tsfx rsfx b1 b2

and m_set (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items) (x: asn1_sequence_t_core items)
: Lemma
  (requires (
    wf_items items /\ asn1_set_k_wf ids /\
    (forall v . TVS.count v (ritems items y) == TVS.count v (items_to_values items x))))
  (ensures (check_items items y == Some x))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    rdec_values dk y;
    Inj.dec_values dk x;
    Inj.short_count_eq (rdec dk y) (dec_to_values dk x);
    m_dec dk y x
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a1, b1) = y' in
    let (a2, b2) = x' in
    let d1 = rdec dk a1 in
    let d2 = dec_to_values dk a2 in
    let t1 = ritems tl b1 in
    let t2 = items_to_values tl b2 in
    rdec_values dk a1;
    Inj.dec_values dk a2;
    rset_items_not_in tl s' b1;
    Inj.set_items_not_in tl s' b2;
    let in_s' (w: asn1_value) : GTot prop = Set.mem (value_id w) s' in
    let not_in_s' (w: asn1_value) : GTot prop = ~ (Set.mem (value_id w) s') in
    let prf (v: asn1_value) : Lemma (TVS.count v d1 == TVS.count v d2 /\ TVS.count v t1 == TVS.count v t2) =
      TVS.count_append v d1 t1;
      TVS.count_append v d2 t2;
      if Set.mem (value_id v) s'
      then begin
        Inj.count_not_mem v t1 not_in_s';
        Inj.count_not_mem v t2 not_in_s'
      end else begin
        Inj.count_not_mem v d1 in_s';
        Inj.count_not_mem v d2 in_s'
      end
    in
    FStar.Classical.forall_intro prf;
    Inj.short_count_eq d1 d2;
    m_dec dk a1 a2;
    m_set tl b1 b2
#pop-options

(* Main theorems *)

let rvalue_check_ser (#s: _) (k: asn1_k s) (u: squash (wf k)) (y: asn1_raw_t k) (x: asn1_t k { encodable k x })
: Lemma
  (requires (check_ser k u y == Some x))
  (ensures (asn1_value_enc (rvalue k y) == asn1_enc k x))
= r1_value k y x

let rvalue_parse (#s: _) (k: asn1_k s) (u: squash (wf k)) (y: asn1_raw_t k) (x: asn1_t k)
: Lemma
  (requires (
    let b = asn1_value_enc (rvalue k y) in
    parse (asn1_as_parser k) b == Some (x, Seq.length b)))
  (ensures (Some? (check_ser k u y) /\ (Some?.v (check_ser k u y) <: asn1_t k) == x))
= let b = asn1_value_enc (rvalue k y) in
  asn1_as_parser_consumed k b;
  Seq.lemma_eq_elim (Seq.slice b 0 (Seq.length b)) b;
  asn1_value_enc_inj (rvalue k y) (to_value k x);
  m_value k y x;
  parsed_encodable k b;
  encodable_conforms k x

(* `check_ser` is the typed parser on the generic encoding of a raw value *)
let check_ser_parse (#s: _) (k: asn1_k s) (u: squash (wf k)) (y: asn1_raw_t k)
: Lemma
  (let b = asn1_value_enc (rvalue k y) in
   match check_ser k u y with
   | Some x -> parse (asn1_as_parser k) b == Some ((x <: asn1_t k), Seq.length b)
   | None ->
     begin match parse (asn1_as_parser k) b with
     | Some (_, n) -> n <> Seq.length b
     | None -> True
     end)
= let b = asn1_value_enc (rvalue k y) in
  match check_ser k u y with
  | Some x -> rvalue_check_ser k u y x
  | None ->
    match parse (asn1_as_parser k) b with
    | Some (x, n) -> if n = Seq.length b then rvalue_parse k u y x
    | None -> ()
