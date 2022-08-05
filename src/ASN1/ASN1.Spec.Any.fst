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
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
//  (pf : List.noRepeats (List.map fst lc))
  : Tot (id : t -> asn1_weak_parser 
                  (refine_with_tag (project_tags lc) id))
= fun id ->
  match lc with
  | [] -> fail_parser _ _
  | hd :: tl ->
    let (id', gp) = hd in
    if (id = id') then
      let p = (Mkgenparser?.p gp) in 
      parse_synth p (attach_tag lc id)
    else      
      parse_synth (make_gen_choice_weak_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x)

let make_gen_choice_weak_parser
  (#t : eqtype)
  (#k : parser_kind)
  (p : parser k t)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  //(pf : List.noRepeats (List.map fst lc))
  : parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type (extract_types lc))
= parse_tagged_union p (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc)

let tag_of_gen_choice_type_with_fallback (#key : eqtype) (lc : list (key & Type)) (fb : Type) : make_gen_choice_type_with_fallback lc fb -> Tot key = dfst

let project_tags_with_fallback (#t : eqtype) (#k : parser_kind) (lc : list (t & (gen_parser k))) (fb : gen_parser k) =
tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)

let attach_tag_with_fallback (#t : eqtype) (#k : parser_kind) (lc : list (t & (gen_parser k))) (fb : gen_parser k) (id : t) (x :  idlookup_with_fallback_t id (extract_types lc) (Mkgenparser?.t fb)) : 
  (refine_with_tag (project_tags_with_fallback lc fb) id)
= Mkdtuple2 id x

let lemma_choice_with_fallback_cast
  (#key : eqtype)
  (hd : key & Type)
  (tl : list (key & Type))
  (fb : Type)
  (id : key)
  (ret : refine_with_tag (tag_of_gen_choice_type_with_fallback tl fb) id)
: Pure (refine_with_tag (tag_of_gen_choice_type_with_fallback (hd :: tl) fb) id)
  (requires id <> (fst hd))
  (ensures (fun _ -> True))
= let (|id', v|) = ret in
  (|id', v|)

let rec make_gen_choice_with_fallback_weak_payload_parser
  (#t : eqtype)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  (fb : gen_parser asn1_weak_parser_kind)
//  (pf : List.noRepeats (List.map fst lc))
  : Tot (id : t -> asn1_weak_parser 
                  (refine_with_tag (project_tags_with_fallback lc fb) id))
= fun id ->
  match lc with
  | [] ->
    assert (lc == []);
    let _ = List.map_lemma (fun x -> (fst x, Mkgenparser?.t (snd x))) lc in
    assert (extract_types lc == []);
    parse_synth (Mkgenparser?.p fb) (attach_tag_with_fallback lc fb id)
  | hd :: tl ->
    let (id', gp) = hd in
    if (id = id') then
      let p = (Mkgenparser?.p gp) in 
      parse_synth p (attach_tag_with_fallback lc fb id)
    else      
      parse_synth (make_gen_choice_with_fallback_weak_payload_parser tl fb id) (fun x -> lemma_choice_with_fallback_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) (Mkgenparser?.t fb) id x)

let make_gen_choice_with_fallback_weak_parser
  (#t : eqtype)
  (#k : parser_kind)
  (p : parser k t)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  (fb : gen_parser asn1_weak_parser_kind)
  //(pf : List.noRepeats (List.map fst lc))
  : parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb))
= parse_tagged_union p (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb)

let make_asn1_closed_any_OIDU32_parser
  (id : asn1_id_t)
  (ls : list (asn1_oid_t * asn1_gen_items_k))
  (pf : squash((List.noRepeats (List.map fst ls))))
  (k : asn1_content_k)
  (lp : list (asn1_oid_t & (gen_parser asn1_weak_parser_kind)))
: Pure (asn1_weak_parser (asn1_content_t k))
  (requires ((k == ASN1_ANY_OID id ls None pf) /\ (asn1_any_t asn1_oid_t ls == extract_types lp)))
  (ensures fun _ -> True)
= weaken asn1_weak_parser_kind (make_gen_choice_weak_parser (parse_asn1_ILC id #(ASN1_TERMINAL ASN1_OID) parse_asn1_OIDU32) lp)

let make_asn1_closed_any_INTEGER_parser
  (id : asn1_id_t)
  (ls : list (asn1_integer_t * asn1_gen_items_k))
  (pf : squash(List.noRepeats (List.map fst ls)))
  (k : asn1_content_k)
  (lp : list (asn1_integer_t & (gen_parser asn1_weak_parser_kind)))
: Pure (asn1_weak_parser (asn1_content_t k))
  (requires ((k == ASN1_ANY_INTEGER id ls None pf) /\ (asn1_any_t asn1_integer_t ls == extract_types lp)))
  (ensures fun _ -> True)
= weaken asn1_weak_parser_kind (make_gen_choice_weak_parser (parse_asn1_ILC id #(ASN1_TERMINAL ASN1_INTEGER) (weaken _ parse_untagged_int32)) lp)

let make_asn1_open_any_OIDU32_parser
  (id : asn1_id_t)
  (ls : list (asn1_oid_t * asn1_gen_items_k))
  (fbk : asn1_gen_items_k)
  (fbp : asn1_weak_parser (asn1_sequence_t (dfst fbk)))
  (pf : squash((List.noRepeats (List.map fst ls))))
  (k : asn1_content_k)
  (lp : list (asn1_oid_t & (gen_parser asn1_weak_parser_kind)))
: Pure (asn1_weak_parser (asn1_content_t k))
  (requires ((k == ASN1_ANY_OID id ls (Some fbk) pf) /\ (asn1_any_t asn1_oid_t ls == extract_types lp)))
  (ensures fun _ -> True)
= weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser (parse_asn1_ILC id #(ASN1_TERMINAL ASN1_OID) parse_asn1_OIDU32) lp (Mkgenparser _ fbp))

let make_asn1_open_any_INTEGER_parser
  (id : asn1_id_t)
  (ls : list (asn1_integer_t * asn1_gen_items_k))
  (fbk : asn1_gen_items_k)
  (fbp : asn1_weak_parser (asn1_sequence_t (dfst fbk)))
  (pf : squash((List.noRepeats (List.map fst ls))))
  (k : asn1_content_k)
  (lp : list (asn1_integer_t & (gen_parser asn1_weak_parser_kind)))
: Pure (asn1_weak_parser (asn1_content_t k))
  (requires ((k == ASN1_ANY_INTEGER id ls (Some fbk) pf) /\ (asn1_any_t asn1_integer_t ls == extract_types lp)))
  (ensures fun _ -> True)
= weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser (parse_asn1_ILC id #(ASN1_TERMINAL ASN1_INTEGER) (weaken _ parse_untagged_int32)) lp (Mkgenparser _ fbp))
