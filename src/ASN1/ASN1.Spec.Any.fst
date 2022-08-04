module ASN1.Spec.Any

open ASN1.Base

open LowParse.Spec.Combinators

open ASN1.Spec.Content.OIDU32
open ASN1.Spec.Content.INTEGER

open ASN1.Spec.ILC
open ASN1.Spec.Choice

module List = FStar.List.Tot

let rec make_gen_choice_weak_payload_parser
  (#t : eqtype)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)) {Cons? lc})
//  (pf : List.noRepeats (List.map fst lc))
  : Tot (id : t -> asn1_weak_parser 
                  (refine_with_tag (project_tags lc) id))
= fun id ->
  match lc with
  | hd :: tl ->
    let (id', gp) = hd in
    if (id = id') then
      let p = (Mkgenparser?.p gp) in 
      parse_synth p (attach_tag lc id)
    else      
      (match tl with
      | nil -> fail_parser asn1_weak_parser_kind (refine_with_tag (project_tags lc) id)
      | _ -> make_gen_choice_weak_payload_parser tl id)

let make_gen_choice_weak_parser
  (#t : eqtype)
  (#k : parser_kind)
  (p : parser k t)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)) {Cons? lc})
  //(pf : List.noRepeats (List.map fst lc))
  : parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type (extract_types lc))
= parse_tagged_union p (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc)

let make_asn1_any_OIDU32_parser
  (id : asn1_id_t)
  (ls : list (asn1_oid_t * asn1_gen_item_k))
  (pf : squash((Cons? ls) /\ (List.noRepeats (List.map fst ls))))
  (k : asn1_content_k)
  (lp : list (asn1_oid_t & (gen_parser asn1_weak_parser_kind)))
: Pure (asn1_weak_parser (asn1_content_t k))
  (requires ((k == ASN1_ANY_OID id ls pf) /\ (asn1_any_t asn1_oid_t ls == extract_types lp)))
  (ensures fun _ -> True)
= weaken asn1_weak_parser_kind (make_gen_choice_weak_parser (parse_asn1_ILC id #(ASN1_TERMINAL ASN1_OID) parse_asn1_OIDU32) lp)

let make_asn1_any_INTEGER_parser
  (id : asn1_id_t)
  (ls : list (asn1_integer_t * asn1_gen_item_k))
  (pf : squash((Cons? ls) /\ (List.noRepeats (List.map fst ls))))
  (k : asn1_content_k)
  (lp : list (asn1_integer_t & (gen_parser asn1_weak_parser_kind)))
: Pure (asn1_weak_parser (asn1_content_t k))
  (requires ((k == ASN1_ANY_INTEGER id ls pf) /\ (asn1_any_t asn1_integer_t ls == extract_types lp)))
  (ensures fun _ -> True)
= weaken asn1_weak_parser_kind (make_gen_choice_weak_parser (parse_asn1_ILC id #(ASN1_TERMINAL ASN1_INTEGER) (weaken _ parse_untagged_int32)) lp)
