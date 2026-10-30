module ASN1.Spec.ToValue

(* Typed ASN.1 values to generic ASN.1 values: the encoder of a typed value
   is the generic encoder (ASN1.Spec.Value.Enc) of its generic value. *)

open ASN1.Base
open ASN1.Spec.Value.Enc
open ASN1.Spec.Content.Enc
open LowParse.Tot.Combinators

module List = FStar.List.Tot
module Seq = FStar.Seq

(* Identifiers of well-formed schemas are valid (see
   ASN1.Spec.Conformance.wf); for other schemas, we use an arbitrary valid
   identifier, so that `to_value` is total. *)
let default_any_id : asn1_any_id_t = MK_ASN1_ID CONTEXT_SPECIFIC PRIMITIVE 0ul

let any_id (id: asn1_id_t) : Tot asn1_any_id_t =
  if asn1_any_id_valid id then id else default_any_id

let mk_prim (id: asn1_id_t) (c: asn1_octetstring_t) : Tot asn1_value =
  ASN1_VALUE_PRIMITIVE (any_id id) c

let mk_cons (id: asn1_id_t) (l: list asn1_value) : Tot asn1_value =
  ASN1_VALUE_CONSTRUCTED (any_id id) l

(* An explicitly tagged value (X.690 8.14): constructed if the outer
   identifier is, otherwise the encoding of the inner value as the
   contents of a primitive value (e.g. OCTET STRING encapsulation) *)
let mk_encap (id: asn1_id_t) (w: asn1_value) : Tot asn1_value =
  if CONSTRUCTED? id.f
  then mk_cons id [w]
  else mk_prim id (asn1_value_enc w)

let rec terminal_to_value (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k) : Tot asn1_value (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_t k2);
    let x' : asn1_terminal_t k2 = FStar.Pervasives.coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k2) () x in
    mk_encap id (terminal_to_value id2 k2 x')
  | _ -> mk_prim id (leaf_enc k x)

(* SET components are encoded in the canonical order of their tags *)

let value_id (v: asn1_value) : Tot asn1_id_t =
  match v with
  | ASN1_VALUE_PRIMITIVE id _ -> id
  | ASN1_VALUE_CONSTRUCTED id _ -> id

let rec insert_by_tag (v: asn1_value) (l: list asn1_value) : Tot (list asn1_value) (decreases l) =
  match l with
  | [] -> [v]
  | w :: q ->
    if asn1_tag_lt (value_id w) (value_id v)
    then w :: insert_by_tag v q
    else v :: l

let rec sort_by_tag (l: list asn1_value) : Tot (list asn1_value) (decreases l) =
  match l with
  | [] -> []
  | v :: q -> insert_by_tag v (sort_by_tag q)

(* Typed values *)

let rec content_to_value (id: asn1_id_t) (k: asn1_content_k) (x: asn1_content_t k) : Tot asn1_value (decreases %[k; 0]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> terminal_to_value id k' x
  | ASN1_TERMINAL k' -> terminal_to_value id k' x
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    mk_cons id (items_to_values items x)
  | ASN1_SET _ items _ -> mk_cons id (sort_by_tag (items_to_values items x))
  | ASN1_SEQUENCE_OF _ k' -> mk_cons id (list_to_values k' x)
  | ASN1_SET_OF _ k' -> mk_cons id (list_to_values k' x)
  | ASN1_PREFIXED k' -> mk_encap id (to_value k' x)
  | ASN1_ANY_DEFINED_BY _ prefix kid key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let sfx (s: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        terminal_to_value kid key_k key :: ls_to_values (key_of_lit key_k) ls key y
      in
      mk_cons id (items_any_to_values prefix sfx x)
    | Some fb ->
      let (| _, fbitems |) = fb in
      let sfx (s: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core fbitems)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        terminal_to_value kid key_k key ::
        ls_fb_to_values (key_of_lit key_k) ls (asn1_sequence_t_core fbitems) (fun (z: asn1_sequence_t_core fbitems) -> items_to_values fbitems z) key y
      in
      mk_cons id (items_any_to_values prefix sfx x)
    end

and list_to_values (#s: _) (k: asn1_k s) (l: list (asn1_t k)) : Tot (list asn1_value) (decreases %[k; l]) =
  match l with
  | [] -> []
  | a :: q -> to_value k a :: list_to_values k q

and to_value (#s: _) (k: asn1_k s) (x: asn1_t k) : Tot asn1_value (decreases %[k; x]) =
  match k with
  | ASN1_ILC id k' -> content_to_value id k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, y |) = x' in
    choice_to_value lc id y
  | ASN1_ANY_ILC -> x

and choice_to_value (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (asn1_lc_t lc)) : Tot asn1_value (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then content_to_value id c y
    else choice_to_value tl id y

and ls_to_values (#lt #t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (key: t) (y: idlookup_t key (asn1_any_t_core t f ls)) : Tot (list asn1_value) (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = f key'
    then items_to_values items y
    else ls_to_values f tl key y

and ls_fb_to_values (#lt #t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk)) (fb: Type) (fbf: fb -> Tot (list asn1_value)) (key: t) (y: idlookup_with_fallback_t key (asn1_any_t_core t f ls) fb) : Tot (list asn1_value) (decreases %[ls; 0]) =
  match ls with
  | [] -> fbf y
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = f key'
    then items_to_values items y
    else ls_fb_to_values f tl fb fbf key y

and dec_to_values (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk) : Tot (list asn1_value) (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> [to_value k x]
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> [] | Some y -> [to_value k y])
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x' : default_tv defv = x in
    (match x' with Default -> [] | Nondefault y -> [terminal_to_value id k y])
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x' : default_tv #(parse_filter_refine (restriction_pred r)) defv = x in
    (match x' with Default -> [] | Nondefault y -> [terminal_to_value id k y])

and items_to_values (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items) : Tot (list asn1_value) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> dec_to_values dk x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    dec_to_values dk a `List.append` items_to_values tl b

and items_any_to_values (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (x: asn1_sequence_any_t_core items sfx_t) : Tot (list asn1_value) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfx x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    let (a, b) = x' in
    dec_to_values dk a `List.append` sfx b
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    let (a, b) = x' in
    dec_to_values dk a `List.append` items_any_to_values tl sfx b
