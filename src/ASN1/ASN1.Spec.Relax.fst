module ASN1.Spec.Relax

(* Schema relaxation, for checked writers.

   `relax k` is a schema with the same Pulse representation types as `k`
   (`ASN1.Pulse.CheckedWriter`), but whose typed values carry fewer
   refinements: a value of `asn1_t (relax k)` need not satisfy the
   schema-specific constraints of `k`, which a checked writer then checks at
   run time, by validating the bytes it wrote against `k`. The relaxation:
   - drops value restrictions (`ASN1_RESTRICTED_TERMINAL`);
   - turns DEFAULT components into OPTIONAL ones (so that the default value
     may be explicitly present);
   - drops the `SIZE (1..MAX)` constraint of SEQUENCE OF and SET OF;
   - widens the bound of small INTEGERs (at most 8 octets) to 8 octets;
   - turns string, time and object identifier kinds into OCTET STRING when
     their tag is not UNIVERSAL. Under a UNIVERSAL tag, the kind must be
     kept, for the schema to stay well-formed (`ASN1.Spec.Conformance.wf`):
     the contents of a UNIVERSAL primitive value are constrained by the
     generic DER value model itself.
   It keeps SET OF values as lists in their encoding order, so their order
   is checked at run time. *)

open ASN1.Base
module Set = FStar.Set

irreducible let asn1_relax_attr : unit = ()

[@@asn1_relax_attr]
let relax_leaf (id: asn1_id_t) (k: asn1_terminal_k) : Tot asn1_terminal_k =
  match id with
  | MK_ASN1_ID UNIVERSAL _ _ -> k
  | _ -> ASN1_OCTETSTRING

[@@asn1_relax_attr]
let relax_integer (bound: pos) : Tot asn1_terminal_k =
  if bound <= 8 then ASN1_INTEGER 8 else ASN1_INTEGER bound

[@@asn1_relax_attr]
let rec relax_terminal (id: asn1_id_t) (k: asn1_terminal_k) : Tot asn1_terminal_k (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> ASN1_PREFIXED_TERMINAL id2 (relax_terminal id2 k2)
  | ASN1_BOOLEAN -> ASN1_BOOLEAN
  | ASN1_NULL -> ASN1_NULL
  | ASN1_BITSTRING -> ASN1_BITSTRING
  | ASN1_INTEGER bound -> relax_integer bound
  | _ -> relax_leaf id k

[@@asn1_relax_attr]
let relax_d (d: asn1_decorator) : Tot asn1_decorator =
  match d with
  | PLAIN -> PLAIN
  | _ -> OPTION

[@@asn1_relax_attr]
let rec relax_ids (ids: id_decs) : Tot id_decs =
  match ids with
  | [] -> []
  | (s, d) :: tl -> (s, relax_d d) :: relax_ids tl

let rec relax_ids_seq_wf' (ids: id_decs) (s: Set.set asn1_id_t)
: Lemma (requires (asn1_sequence_k_wf' ids s)) (ensures (asn1_sequence_k_wf' (relax_ids ids) s)) (decreases ids)
= match ids with
  | [] -> ()
  | (s', d) :: tl ->
    begin match d with
    | PLAIN -> relax_ids_seq_wf tl
    | _ -> relax_ids_seq_wf' tl (Set.union s s')
    end

and relax_ids_seq_wf (ids: id_decs)
: Lemma (requires (asn1_sequence_k_wf ids)) (ensures (asn1_sequence_k_wf (relax_ids ids))) (decreases ids)
= match ids with
  | [] -> ()
  | (s', d) :: tl ->
    begin match d with
    | PLAIN -> relax_ids_seq_wf tl
    | _ -> relax_ids_seq_wf' tl s'
    end

let rec relax_ids_set_wf' (s: Set.set asn1_id_t) (ids: id_decs)
: Lemma (requires (asn1_set_k_wf' s ids)) (ensures (asn1_set_k_wf' s (relax_ids ids))) (decreases ids)
= match ids with
  | [] -> ()
  | _ :: tl -> relax_ids_set_wf' s tl

let rec relax_ids_set_wf (ids: id_decs)
: Lemma (requires (asn1_set_k_wf ids)) (ensures (asn1_set_k_wf (relax_ids ids))) (decreases ids)
= match ids with
  | [] -> ()
  | (s, _) :: tl -> relax_ids_set_wf' s tl; relax_ids_set_wf tl

[@@asn1_relax_attr]
let relax_seq_ids (ids: id_decs { asn1_sequence_k_wf ids }) : Tot (ids': id_decs { asn1_sequence_k_wf ids' /\ ids' == relax_ids ids }) =
  relax_ids_seq_wf ids;
  relax_ids ids

[@@asn1_relax_attr]
let relax_set_pf (ids: id_decs) (pf: squash (asn1_set_k_wf ids)) : Tot (squash (asn1_set_k_wf (relax_ids ids))) =
  relax_ids_set_wf ids

[@@asn1_relax_attr]
let rec relax_content (id: asn1_id_t) (k: asn1_content_k) : Tot asn1_content_k (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> ASN1_TERMINAL (relax_terminal id k')
  | ASN1_TERMINAL k' -> ASN1_TERMINAL (relax_terminal id k')
  | ASN1_SEQUENCE gitems ->
    ASN1_SEQUENCE (| relax_seq_ids (Mkdtuple2?._1 gitems), relax_items (Mkdtuple2?._2 gitems) |)
  | ASN1_SET ids items pf -> ASN1_SET (relax_ids ids) (relax_items items) (relax_set_pf ids pf)
  | ASN1_SEQUENCE_OF _ k' -> ASN1_SEQUENCE_OF false (relax k')
  | ASN1_SET_OF _ k' -> ASN1_SET_OF false (relax k')
  | ASN1_PREFIXED k' -> ASN1_PREFIXED (relax k')
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ _ _ _ -> k

and relax_lc (lc: list (asn1_id_t & asn1_content_k))
: Tot (lc': list (asn1_id_t & asn1_content_k) { List.Tot.map fst lc' == List.Tot.map fst lc }) (decreases lc)
= match lc with
  | [] -> []
  | (id, c) :: tl -> (id, relax_content id c) :: relax_lc tl

and relax (#s: _) (k: asn1_k s) : Tot (asn1_k s) (decreases k) =
  match k with
  | ASN1_ILC id c -> ASN1_ILC id (relax_content id c)
  | ASN1_CHOICE_ILC lc pf ->
    let lc' = relax_lc lc in
    FStar.Pervasives.coerce_eq #(asn1_k (my_as_set (List.Tot.map fst lc'))) #(asn1_k s) () (ASN1_CHOICE_ILC lc' ())
  | ASN1_ANY_ILC -> ASN1_ANY_ILC

and relax_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot (asn1_decorated_k s (relax_d d)) (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> ASN1_PLAIN_ILC (relax k)
  | ASN1_OPTION_ILC k -> ASN1_OPTION_ILC (relax k)
  | ASN1_DEFAULT_TERMINAL id #k _ -> ASN1_OPTION_ILC (ASN1_ILC id (ASN1_TERMINAL (relax_terminal id k)))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k _ _ -> ASN1_OPTION_ILC (ASN1_ILC id (ASN1_TERMINAL (relax_terminal id k)))

and relax_items (#ids: _) (items: asn1_gen_items_l ids) : Tot (asn1_gen_items_l (relax_ids ids)) (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> ASN1_GEN_ITEMS_NIL
  | ASN1_GEN_ITEMS_CONS s d dk tl rest ->
    ASN1_GEN_ITEMS_CONS s (relax_d d) (relax_dec dk) (relax_ids tl) (relax_items rest)
