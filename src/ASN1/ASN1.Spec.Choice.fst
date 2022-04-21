module ASN1.Spec.Choice

open ASN1.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators

open ASN1.Spec.IdentifierU32

module Math = FStar.Math.Lib
module List = FStar.List.Tot

(*

let sanitify_parser_kind (k : parser_kind)
: Pure parser_kind
  (requires True)
  (ensures fun k -> fail_parser_kind_precond k)
= {
  parser_kind_low = k.parser_kind_low;
  parser_kind_high = k.parser_kind_high;
  parser_kind_subkind = k.parser_kind_subkind;
  parser_kind_metadata = (match k.parser_kind_metadata with Some ParserKindMetadataFail -> Some ParserKindMetadataFail | _ -> None);
  }

let rec make_gen_choice_kind
  (lc : list gen_parser {Cons? lc})
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    fail_parser_kind_precond k /\
    (let lk = List.map Mkgenparser?.k lc in
    forall k'. {:pattern (List.memP k' lk)} (List.memP k' lk) ==> is_weaker_than k k')))
= match lc with
  | [h] -> 
    let k = Mkgenparser?.k h in
    sanitify_parser_kind k
  | h :: t -> glb (Mkgenparser?.k h) (make_gen_choice_kind t)

*)

let tag_of_gen_choice_type (#key : eqtype) (lc : list (key & Type)) : make_gen_choice_type lc -> Tot key = dfst

let extract_types (#t : eqtype) (lc : list (t & gen_parser)) =
  List.map (fun x -> (fst x, Mkgenparser?.t (snd x))) lc

let project_tags (#t : eqtype) (lc : list (t & gen_parser)) =
tag_of_gen_choice_type (extract_types lc)

let attach_tag (#t : eqtype) (lc : list (t & gen_parser)) (id : t) (x :  idlookup_t id (extract_types lc)) : 
  (refine_with_tag (project_tags lc) id)
= Mkdtuple2 id x

let rec make_gen_choice_payload_parser
  (#t : eqtype)
  (lc : list (t & gen_parser) {Cons? lc})
//  (pf : List.noRepeats (List.map fst lc))
  : Tot (id : t -> asn1_strong_parser 
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
      | nil -> fail_parser asn1_strong_parser_kind (refine_with_tag (project_tags lc) id)
      | _ -> make_gen_choice_payload_parser tl id)

let make_gen_choice_parser
  (#t : eqtype)
  (#k : parser_kind)
  (p : parser k t)
  (lc : list (t & gen_parser) {Cons? lc})
  //(pf : List.noRepeats (List.map fst lc))
  : parser (and_then_kind k asn1_strong_parser_kind) (make_gen_choice_type (extract_types lc))
= parse_tagged_union p (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_payload_parser lc)

let make_asn1_choice_parser
  (lc : list (asn1_id_t * asn1_content_k) {Cons? lc})
  (pf : ((Cons? lc) /\ List.noRepeats (List.map fst lc)))
  (#s : _)
  (k : asn1_k s)
  (lp : list (asn1_id_t & gen_parser) {Cons? lp})
  : 
  Pure (asn1_strong_parser (asn1_t k))
  (requires (s == Set.as_set (List.map fst lc)) /\ (k == ASN1_CHOICE_ILC lc pf) /\ (asn1_lc_t lc == extract_types lp))
  (ensures fun _ -> True)
= weaken asn1_strong_parser_kind (make_gen_choice_parser parse_asn1_identifier_u21 lp)

let make_asn1_choice_parser_twin
  (lc : list (asn1_id_t * asn1_content_k) {Cons? lc})
  (pf : ((Cons? lc) /\ List.noRepeats (List.map fst lc)))
  (#s : _)
  (k : asn1_k s)
  (lp : list (asn1_id_t & gen_parser) {Cons? lp})
  (id' : asn1_id_t)
  : 
  Pure (asn1_strong_parser (asn1_t k))
  (requires (s == Set.as_set (List.map fst lc)) /\ (k == ASN1_CHOICE_ILC lc pf) /\ (asn1_lc_t lc == extract_types lp))
  (ensures fun _ -> True)
= parse_tagged_union_payload (project_tags lp) (make_gen_choice_payload_parser lp) id'

let make_asn1_choice_parser_twin_cases_injective
  (lc : list (asn1_id_t * asn1_content_k) {Cons? lc})
  (pf : ((Cons? lc) /\ List.noRepeats (List.map fst lc)))
  (#s : _)
  (k : asn1_k s)
  (lp : list (asn1_id_t & gen_parser) {Cons? lp})
  : 
  Lemma 
  (requires (s == Set.as_set (List.map fst lc)) /\ (k == ASN1_CHOICE_ILC lc pf) /\ (asn1_lc_t lc == extract_types lp))
  (ensures and_then_cases_injective (make_asn1_choice_parser_twin lc pf k lp))
= parse_tagged_union_payload_and_then_cases_injective (project_tags lp) (make_gen_choice_payload_parser lp)