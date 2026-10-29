module ASN1.Syntax
open ASN1.Base

module U32 = FStar.UInt32
module List = FStar.List.Tot
module T = FStar.Tactics

// for identifiers

// X.680 §8.6: UNIVERSAL 0 is reserved for use by the encoding rules.
let id_value_ok (c : asn1_id_class_t) (v : U32.t) : bool
= not (c = UNIVERSAL && U32.v v = 0)

let mk_constant_id (x : UInt.uint_t 32 {x <> 0}) : asn1_id_t
= MK_ASN1_ID UNIVERSAL PRIMITIVE (U32.uint_to_t x)

let mk_constant_constructed_id (x : UInt.uint_t 32 {x <> 0}) : asn1_id_t
= MK_ASN1_ID UNIVERSAL CONSTRUCTED (U32.uint_to_t x)

let mk_custom_id (c : asn1_id_class_t) (f : asn1_id_flag_t) (x : UInt.uint_t 32 {id_value_ok c (U32.uint_to_t x)}) : asn1_id_t
= MK_ASN1_ID c f (U32.uint_to_t x)

// X.690 §8.1.2.5: the primitive/constructed bit of an identifier is
// determined by the encoding of its content.

let terminal_flag (k : asn1_terminal_k) : asn1_id_flag_t
= match k with
  | ASN1_PREFIXED_TERMINAL _ _ -> CONSTRUCTED
  | _ -> PRIMITIVE

let content_flag (c : asn1_content_k) : asn1_id_flag_t
= match c with
  | ASN1_RESTRICTED_TERMINAL k _
  | ASN1_TERMINAL k -> terminal_flag k
  | _ -> CONSTRUCTED

let id_ok (id : asn1_id_t) (f : asn1_id_flag_t) : bool
= MK_ASN1_ID?.f id = f && id_value_ok (MK_ASN1_ID?.c id) (MK_ASN1_ID?.v id)

// An OCTET STRING whose content is the DER encoding of a value (e.g. the
// X.509 extnValue) is modeled as a PREFIXED content with a primitive tag.
let is_octetstring_encapsulation (id : asn1_id_t) (c : asn1_content_k) : bool
= match c with
  | ASN1_PREFIXED _ -> id = MK_ASN1_ID UNIVERSAL PRIMITIVE 4ul
  | _ -> false

let id_content_ok (id : asn1_id_t) (c : asn1_content_k) : bool
= id_ok id (content_flag c) || is_octetstring_encapsulation id c

// Whole-schema check that every identifier is consistent with its content.
let rec asn1_terminal_k_wf (k : asn1_terminal_k) : Tot bool (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id k' -> id_ok id (terminal_flag k') && asn1_terminal_k_wf k'
  | _ -> true

let rec asn1_content_k_wf (c : asn1_content_k) : Tot bool (decreases c)
= match c with
  | ASN1_RESTRICTED_TERMINAL k _
  | ASN1_TERMINAL k -> asn1_terminal_k_wf k
  | ASN1_SEQUENCE gitems -> asn1_gen_items_l_wf (dsnd gitems)
  | ASN1_SET _ items _ -> asn1_gen_items_l_wf items
  | ASN1_SEQUENCE_OF _ k
  | ASN1_SET_OF _ k
  | ASN1_PREFIXED k -> asn1_k_wf k
  | ASN1_ANY_DEFINED_BY _ prefix id key_k supported fallback _ _ ->
    asn1_gen_items_l_wf prefix &&
    id_ok id (terminal_flag key_k) && asn1_terminal_k_wf key_k &&
    asn1_supported_wf key_k supported &&
    (match fallback with
     | None -> true
     | Some fb -> asn1_gen_items_l_wf (dsnd fb))

and asn1_supported_wf (key_k : asn1_terminal_k) (l : list (asn1_key_lit key_k & asn1_gen_items_lk)) : Tot bool (decreases l)
= match l with
  | [] -> true
  | (_, gitems) :: tl -> asn1_gen_items_l_wf (dsnd gitems) && asn1_supported_wf key_k tl

and asn1_lc_wf (l : list (asn1_id_t & asn1_content_k)) : Tot bool (decreases l)
= match l with
  | [] -> true
  | (id, c) :: tl -> id_content_ok id c && asn1_content_k_wf c && asn1_lc_wf tl

and asn1_k_wf (#s : _) (k : asn1_k s) : Tot bool (decreases k)
= match k with
  | ASN1_ILC id c -> id_content_ok id c && asn1_content_k_wf c
  | ASN1_CHOICE_ILC lc _ -> asn1_lc_wf lc
  | ASN1_ANY_ILC -> true

and asn1_decorated_k_wf (#s : _) (#d : _) (k : asn1_decorated_k s d) : Tot bool (decreases k)
= match k with
  | ASN1_PLAIN_ILC k'
  | ASN1_OPTION_ILC k' -> asn1_k_wf k'
  | ASN1_DEFAULT_TERMINAL id #k' _
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k' _ _ -> id_ok id (terminal_flag k') && asn1_terminal_k_wf k'

and asn1_gen_items_l_wf (#l : _) (items : asn1_gen_items_l l) : Tot bool (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ hd _ tl -> asn1_decorated_k_wf hd && asn1_gen_items_l_wf tl

noextract
let wf_tac () = T.norm [iota;zeta;delta;primops;simplify]; T.trivial ()

// for INTEGER key literals of ANY DEFINED BY: the DER content bytes

let mk_int_lit (bound : pos) (l : list FStar.UInt8.t) (pf : squash (int_lit_ok bound l)) : asn1_int_lit bound = l

// for OID definitions

let mk_oid (l : list (UInt.uint_t 32)) : Pure (asn1_oid_t)
  (requires asn1_OID_wf (List.map U32.uint_to_t l))
  (ensures fun _ -> True)
= List.map U32.uint_to_t l
let mk_oid_app (oid : asn1_oid_t) (x : UInt.uint_t 32) : asn1_oid_t
= norm [zeta;iota;delta;primops;nbe] (List.append oid [U32.uint_to_t x])
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

let mk_prefixed (id : asn1_id_t {id_ok id CONSTRUCTED}) (#s) (x : asn1_k s)
= ASN1_ILC id (ASN1_PREFIXED x)

let mk_retagged (id : asn1_id_t) (#s) (x : asn1_k s {is_ILC x /\ id_content_ok id (proj_content x)})
= ASN1_ILC id (proj_content x)

let op_Star_Hat (name : string) (#t) (x : t)
= x

let op_Hat_Star (name : string) (#s) (x : asn1_k s {is_ILC x}) : (asn1_id_t & asn1_content_k)
= match x with
  | ASN1_ILC id c -> (id, c)

noextract
let choice_tac () = T.norm [iota;zeta;delta;primops]; T.trefl () 

let asn1_choice (ls : list (asn1_id_t & asn1_content_k)) (pf : squash (List.noRepeats (List.map fst ls) ))
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
= ASN1_DEFAULT_RESTRICTED_TERMINAL (proj_identifier x) #(proj_terminal_k x) (RESTRICT_CUSTOM f) v

let mk_restricted_field (#s) (x : asn1_k s {is_terminal x}) (f : proj_terminal_t x -> bool)
= ASN1_ILC (proj_identifier x) (ASN1_RESTRICTED_TERMINAL (proj_terminal_k x) (RESTRICT_CUSTOM f))

(* Restrictions given as first-class descriptors (see asn1_restriction),
   which validator generators can implement *)
let mk_restriction_default_field (#s) (x : asn1_k s {is_terminal x}) (r : asn1_restriction (proj_terminal_k x)) (v : proj_terminal_t x {restriction_pred r v})
= ASN1_DEFAULT_RESTRICTED_TERMINAL (proj_identifier x) #(proj_terminal_k x) r v

let mk_restriction_field (#s) (x : asn1_k s {is_terminal x}) (r : asn1_restriction (proj_terminal_k x))
= ASN1_ILC (proj_identifier x) (ASN1_RESTRICTED_TERMINAL (proj_terminal_k x) r)

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

let set_tac () = seq_tac ()

let mk_gen_items (items : list asn1_gen_item_k) (pf : squash (asn1_sequence_k_wf (List.map proj2_of_3 items)))
: asn1_gen_items_lk
= k_as_lk (| items, pf |)

// constants

let boolean_id = mk_constant_id 1

let asn1_boolean = ASN1_ILC boolean_id (ASN1_TERMINAL ASN1_BOOLEAN)

let integer_id = mk_constant_id 2

let asn1_bounded_integer (bound : pos) = ASN1_ILC integer_id (ASN1_TERMINAL (ASN1_INTEGER bound))

let asn1_integer = asn1_bounded_integer asn1_any_integer_bound

let bitstring_id = mk_constant_id 3

let asn1_bitstring = ASN1_ILC bitstring_id (ASN1_TERMINAL ASN1_BITSTRING)

let octetstring_id = mk_constant_id 4

let asn1_octetstring = ASN1_ILC octetstring_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let null_id = mk_constant_id 5

let asn1_null = ASN1_ILC null_id (ASN1_TERMINAL ASN1_NULL)

let oid_id = mk_constant_id 6

let asn1_oid = ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

let objectdescriptor_id = mk_constant_id 7

let asn1_objectdescriptor = ASN1_ILC objectdescriptor_id (ASN1_TERMINAL ASN1_OBJECTDESCRIPTOR)

let enumerated_id = mk_constant_id 10

(* ENUMERATED { ... } (X.680 20) with the given admissible values; its
   contents are encoded as those of an INTEGER (X.690 8.4) *)
let asn1_enumerated (values : list int)
= ASN1_ILC enumerated_id (ASN1_RESTRICTED_TERMINAL (ASN1_INTEGER asn1_any_integer_bound) (RESTRICT_INT_IN values))

let utf8string_id = mk_constant_id 12

let asn1_utf8string = ASN1_ILC utf8string_id (ASN1_TERMINAL ASN1_UTF8STRING)

let relative_oid_id = mk_constant_id 13

let asn1_relative_oid = ASN1_ILC relative_oid_id (ASN1_TERMINAL ASN1_RELATIVE_OID)

let sequence_id = mk_constant_constructed_id 16

let asn1_sequence (items : list asn1_gen_item_k) (pf : squash (asn1_sequence_k_wf (List.map proj2_of_3 items)))
= ASN1_ILC sequence_id (ASN1_SEQUENCE (k_as_lk (| items, pf |) ))

// SEQUENCE OF / SET OF, possibly empty
let asn1_sequence_of (#s) (item : asn1_k s) = ASN1_ILC sequence_id (ASN1_SEQUENCE_OF false item)

// SEQUENCE SIZE (1..MAX) OF
let asn1_nonempty_sequence_of (#s) (item : asn1_k s) = ASN1_ILC sequence_id (ASN1_SEQUENCE_OF true item)

let set_id = mk_constant_constructed_id 17

let asn1_set_of (#s) (item : asn1_k s) = ASN1_ILC set_id (ASN1_SET_OF false item)

// SET SIZE (1..MAX) OF
let asn1_nonempty_set_of (#s) (item : asn1_k s) = ASN1_ILC set_id (ASN1_SET_OF true item)

// SET { ... }: the components must have distinct tags (use `set_tac`)
let asn1_set (items : list asn1_gen_item_k) (pf : squash (asn1_set_k_wf (List.map proj2_of_3 items)))
= ASN1_ILC set_id (ASN1_SET _ (list_as_l items) pf)

let numericstring_id = mk_constant_id 18

let asn1_numericstring = ASN1_ILC numericstring_id (ASN1_TERMINAL ASN1_NUMERICSTRING)

let printablestring_id = mk_constant_id 19

let asn1_printablestring = ASN1_ILC printablestring_id (ASN1_TERMINAL ASN1_PRINTABLESTRING)

let teletexstring_id = mk_constant_id 20

let asn1_teletexstring = ASN1_ILC teletexstring_id (ASN1_TERMINAL ASN1_TELETEXSTRING)

let videotexstring_id = mk_constant_id 21

let asn1_videotexstring = ASN1_ILC videotexstring_id (ASN1_TERMINAL ASN1_VIDEOTEXSTRING)

let ia5string_id = mk_constant_id 22

let asn1_ia5string = ASN1_ILC ia5string_id (ASN1_TERMINAL ASN1_IA5STRING)

let utctime_id = mk_constant_id 23

let asn1_utctime = ASN1_ILC utctime_id (ASN1_TERMINAL ASN1_UTCTIME)

let generalizedtime_id = mk_constant_id 24

let asn1_generalizedtime = ASN1_ILC generalizedtime_id (ASN1_TERMINAL ASN1_GENERALIZEDTIME)

let graphicstring_id = mk_constant_id 25

let asn1_graphicstring = ASN1_ILC graphicstring_id (ASN1_TERMINAL ASN1_GRAPHICSTRING)

let visiblestring_id = mk_constant_id 26

let asn1_visiblestring = ASN1_ILC visiblestring_id (ASN1_TERMINAL ASN1_VISIBLESTRING)

let generalstring_id = mk_constant_id 27

let asn1_generalstring = ASN1_ILC generalstring_id (ASN1_TERMINAL ASN1_GENERALSTRING)

let universalstring_id = mk_constant_id 28

let asn1_universalstring = ASN1_ILC universalstring_id (ASN1_TERMINAL ASN1_UNIVERSALSTRING)

let bMPstring_id = mk_constant_id 30

let asn1_bMPstring = ASN1_ILC bMPstring_id (ASN1_TERMINAL ASN1_BMPSTRING)

let date_id = mk_constant_id 31

let asn1_date = ASN1_ILC date_id (ASN1_TERMINAL ASN1_DATE)

let time_of_day_id = mk_constant_id 32

let asn1_time_of_day = ASN1_ILC time_of_day_id (ASN1_TERMINAL ASN1_TIME_OF_DAY)

let date_time_id = mk_constant_id 33

let asn1_date_time = ASN1_ILC date_time_id (ASN1_TERMINAL ASN1_DATE_TIME)

let oid_iri_id = mk_constant_id 35

let asn1_oid_iri = ASN1_ILC oid_iri_id (ASN1_TERMINAL ASN1_OID_IRI)

let relative_oid_iri_id = mk_constant_id 36

let asn1_relative_oid_iri = ASN1_ILC relative_oid_iri_id (ASN1_TERMINAL ASN1_RELATIVE_OID_IRI)

// for any

let asn1_any = ASN1_ANY_ILC

let asn1_any_oid_prefix
  (prefix : list asn1_gen_item_k)
  (name : string)
  (supported : list (asn1_oid_t & asn1_gen_items_lk)) 
  (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id) (List.map proj2_of_3 prefix)))
  (pf_sup : squash (List.noRepeats (List.map fst supported)))
= ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l prefix) oid_id ASN1_OID supported None pf_wf pf_sup)

let asn1_any_oid
  (name : string)
  (supported : list (asn1_oid_t & asn1_gen_items_lk)) 
  (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id) (List.map proj2_of_3 [])))
  (pf_sup : squash (List.noRepeats (List.map fst supported)))
= ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) oid_id ASN1_OID supported None pf_wf pf_sup)

let asn1_any_oid_with_fallback
  (name : string)
  (supported : list (asn1_oid_t & asn1_gen_items_lk)) 
  (fallback : asn1_gen_items_lk)
  (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id) (List.map proj2_of_3 [])))
  (pf_sup : squash (List.noRepeats (List.map fst supported)))
= ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) oid_id ASN1_OID supported (Some fallback) pf_wf pf_sup)
