module ASN1.Syntax

open ASN1.Base

module U32 = FStar.UInt32
module List = FStar.List.Tot
module T = FStar.Tactics

// for identifiers

let mk_constant_id (x : UInt.uint_t 32) : asn1_id_t
= MK_ASN1_ID UNIVERSAL PRIMITIVE (U32.uint_to_t x)

let mk_constant_constructed_id (x : UInt.uint_t 32) : asn1_id_t
= MK_ASN1_ID UNIVERSAL CONSTRUCTED (U32.uint_to_t x)

let mk_custom_id (c : asn1_id_class_t) (f : asn1_id_flag_t) (x : UInt.uint_t 32) : asn1_id_t
= MK_ASN1_ID c f (U32.uint_to_t x)

// for OID definitions

let mk_oid (l : list (UInt.uint_t 32)) : Pure (asn1_oid_t)
  (requires asn1_OID_wf (List.map U32.uint_to_t l))
  (ensures fun _ -> True)
= List.map U32.uint_to_t l

let mk_oid_app (oid : asn1_oid_t) (x : UInt.uint_t 32) : asn1_oid_t
= norm[zeta;iota;delta;primops;nbe] (List.append oid [U32.uint_to_t x])

let op_Slash_Plus = mk_oid_app

// for choices

let is_ILC (#s) (x : asn1_k s)
= match x with
  | ASN1_ILC _ _ -> true
  | _ -> false

let proj_identifier (#s) (x : asn1_k s {is_ILC x}) 
= match x with
  | ASN1_ILC id c -> id

let proj_content (#s) (x : asn1_k s {is_ILC x}) 
= match x with
  | ASN1_ILC id c -> c

let mk_prefixed (id : asn1_id_t) (#s) (x : asn1_k s)
= ASN1_ILC id (ASN1_PREFIXED x)

let mk_retagged (id : asn1_id_t) (#s) (x : asn1_k s {is_ILC x})
= ASN1_ILC id (proj_content x)

let op_Star_Hat (name : string) (#t) (x : t)
= x

let op_Hat_Star (name : string) (#s) (x : asn1_k s {is_ILC x}) : (asn1_id_t * asn1_content_k)
= match x with
  | ASN1_ILC id c -> (id, c)

noextract
let choice_tac () = T.norm [iota;zeta;delta;primops]; T.trefl () 

let asn1_choice (ls : list (asn1_id_t * asn1_content_k)) (pf : squash (List.noRepeats (List.map fst ls) ))
= ASN1_CHOICE_ILC ls pf

// for sequences

let is_terminal (#s) (x : asn1_k s)
= if is_ILC x then
    match (proj_content x) with
    | ASN1_TERMINAL _ -> true
    | _ -> false
  else
    false

let proj_terminal_k (#s) (x : asn1_k s {is_terminal x})
= match proj_content x with
  | ASN1_TERMINAL tk -> tk

let proj_terminal_t (#s) (x : asn1_k s {is_terminal x})
= match proj_content x with
  | ASN1_TERMINAL tk -> asn1_terminal_t tk

let mk_default_field (#s) (x : asn1_k s {is_terminal x}) (v : proj_terminal_t x)
= ASN1_DEFAULT_TERMINAL (proj_identifier x) #(proj_terminal_k x) v

let mk_restricted_default_field (#s) (x : asn1_k s {is_terminal x}) (f : proj_terminal_t x -> bool) (v : proj_terminal_t x {f v})
= ASN1_DEFAULT_RESTRICTED_TERMINAL (proj_identifier x) #(proj_terminal_k x) f v

let mk_restricted_field (#s) (x : asn1_k s {is_terminal x}) (f : proj_terminal_t x -> bool)
= ASN1_ILC (proj_identifier x) (ASN1_RESTRICTED_TERMINAL (proj_terminal_k x) f)

let field_type (s : Set.set asn1_id_t) (d : asn1_decorator) 
= match d with
  | DEFAULT -> asn1_decorated_k s d
  | _ -> asn1_k s

let op_Hat_Colon (#s : Set.set asn1_id_t)  
  (d : asn1_decorator) 
  (f : field_type s d)
: asn1_gen_item_k
= match d with
  | DEFAULT -> mk_ASN1_GEN_ITEM #s #d f
  | PLAIN -> mk_ASN1_GEN_ITEM (ASN1_PLAIN_ILC #s f)
  | OPTION -> mk_ASN1_GEN_ITEM (ASN1_OPTION_ILC #s f)

noextract
let seq_tac () =  T.norm[iota;zeta;delta;primops;simplify]; T.smt()

let mk_gen_items (items : list asn1_gen_item_k) (pf : squash (asn1_sequence_k_wf (List.map proj2_of_3 items))) : asn1_gen_items_k
= (| items, pf |)

// constants

let boolean_id = mk_constant_id 1

let asn1_boolean = ASN1_ILC boolean_id (ASN1_TERMINAL ASN1_BOOLEAN)

let integer_id = mk_constant_id 2

let asn1_integer = ASN1_ILC integer_id (ASN1_TERMINAL ASN1_INTEGER)

let bitstring_id = mk_constant_id 3

let asn1_bitstring = ASN1_ILC bitstring_id (ASN1_TERMINAL ASN1_BITSTRING)

let octetstring_id = mk_constant_id 4

let asn1_octetstring = ASN1_ILC octetstring_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let null_id = mk_constant_id 5

let asn1_null = ASN1_ILC null_id (ASN1_TERMINAL ASN1_NULL)

let oid_id = mk_constant_id 6

let asn1_oid = ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

let utf8string_id = mk_constant_id 12

let asn1_utf8string = ASN1_ILC utf8string_id (ASN1_TERMINAL ASN1_UTF8STRING)

let sequence_id = mk_constant_constructed_id 16

let asn1_sequence (items : list asn1_gen_item_k) (pf : squash (asn1_sequence_k_wf (List.map proj2_of_3 items)))
= ASN1_ILC sequence_id (ASN1_SEQUENCE (| items, pf |))

let asn1_sequence_of (#s) (item : asn1_k s) = ASN1_ILC sequence_id (ASN1_SEQUENCE_OF item)

let set_id = mk_constant_constructed_id 17

let asn1_set_of (#s) (item : asn1_k s) = ASN1_ILC set_id (ASN1_SET_OF item)

let printablestring_id = mk_constant_id 19

let asn1_printablestring = ASN1_ILC printablestring_id (ASN1_TERMINAL ASN1_PRINTABLESTRING)

let teletexstring_id = mk_constant_id 20

let asn1_teletexstring = ASN1_ILC teletexstring_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let ia5string_id = mk_constant_id 22

let asn1_ia5string = ASN1_ILC ia5string_id (ASN1_TERMINAL ASN1_IA5STRING)

let utctime_id = mk_constant_id 23

let asn1_utctime = ASN1_ILC utctime_id (ASN1_TERMINAL ASN1_UTCTIME)

let generalizedtime_id = mk_constant_id 24

let asn1_generalizedtime = ASN1_ILC generalizedtime_id (ASN1_TERMINAL ASN1_GENERALIZEDTIME)

let visiblestring_id = mk_constant_id 26

let asn1_visiblestring = ASN1_ILC visiblestring_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let universalstring_id = mk_constant_id 28

let asn1_universalstring = ASN1_ILC universalstring_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let bMPstring_id = mk_constant_id 30

let asn1_bMPstring = ASN1_ILC bMPstring_id (ASN1_TERMINAL ASN1_OCTETSTRING)

// for any

let asn1_any = ASN1_ANY_ILC

let asn1_any_oid_prefix
  (prefix : list asn1_gen_item_k)
  (name : string)
  (supported : list (asn1_oid_t * asn1_gen_items_k)) 
  (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id) (List.map proj2_of_3 prefix)))
  (pf_sup : squash (List.noRepeats (List.map fst supported)))
= ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY prefix oid_id ASN1_OID supported None pf_wf pf_sup)

let asn1_any_oid
  (name : string)
  (supported : list (asn1_oid_t * asn1_gen_items_k)) 
  (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id) (List.map proj2_of_3 [])))
  (pf_sup : squash (List.noRepeats (List.map fst supported)))
= ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY [] oid_id ASN1_OID supported None pf_wf pf_sup)

let asn1_any_oid_with_fallback
  (name : string)
  (supported : list (asn1_oid_t * asn1_gen_items_k)) 
  (fallback : asn1_gen_items_k)
  (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id) (List.map proj2_of_3 [])))
  (pf_sup : squash (List.noRepeats (List.map fst supported)))
= ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY [] oid_id ASN1_OID supported (Some fallback) pf_wf pf_sup)
