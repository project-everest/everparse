module ASN1.Spec.Interpreter

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.List
include LowParse.Spec.Defaultable
include LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Content.BOOLEAN
open ASN1.Spec.Content.INTEGER
open ASN1.Spec.Content.BITSTRING
open ASN1.Spec.Content.OCTETSTRING
open ASN1.Spec.Content.UTF8STRING
open ASN1.Spec.Content.PRINTABLESTRING
open ASN1.Spec.Content.IA5STRING
open ASN1.Spec.Content.NULL
open ASN1.Spec.Content.OIDU32
open ASN1.Spec.Content.TIME

open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.Any

module List = FStar.List.Tot

let rec asn1_terminal_as_parser (k : asn1_terminal_k) : asn1_weak_parser (asn1_terminal_t k)  =
  match k with
  | ASN1_BOOLEAN -> weaken _ parse_asn1_boolean
  | ASN1_INTEGER -> weaken _ ((parse_untagged_bounded_integer 20) `parse_synth` (fun x -> x <: int))
  | ASN1_BITSTRING -> parse_asn1_bitstring
  | ASN1_OCTETSTRING -> parse_asn1_octetstring
  | ASN1_UTF8STRING -> parse_asn1_utf8string
  | ASN1_PRINTABLESTRING -> parse_asn1_printablestring
  | ASN1_IA5STRING -> parse_asn1_ia5string
  | ASN1_NULL -> parse_asn1_null
  | ASN1_OID -> parse_asn1_OIDU32
  | ASN1_UTCTIME -> parse_asn1_UTCTIME
  | ASN1_GENERALIZEDTIME -> parse_asn1_GENERALIZEDTIME
  | ASN1_PREFIXED_TERMINAL id k -> weaken asn1_weak_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k))

and asn1_content_as_parser (k : asn1_content_k) : Tot (asn1_weak_parser (asn1_content_t k)) (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' is_valid -> weaken _ ((asn1_terminal_as_parser k') `parse_filter` is_valid)
  | ASN1_TERMINAL k' -> asn1_terminal_as_parser k'
  | ASN1_SEQUENCE gitems -> make_asn1_sequence_parser (asn1_sequence_as_parser (dfst gitems))
  | ASN1_SEQUENCE_OF k' -> weaken asn1_weak_parser_kind (parse_list (asn1_as_parser k'))
  | ASN1_SET_OF k' -> weaken _ (asn1_as_parser k')
  | ASN1_PREFIXED k' -> weaken _ (asn1_as_parser k')
  | ASN1_ANY_OID id ls fb pf -> 
    (match fb with
    | None -> make_asn1_closed_any_OIDU32_parser id ls pf k (asn1_ls_as_parser asn1_oid_t ls)
    | Some gitems -> make_asn1_open_any_OIDU32_parser id ls gitems (make_asn1_sequence_parser (asn1_sequence_as_parser (dfst gitems))) pf k (asn1_ls_as_parser asn1_oid_t ls))
  | ASN1_ANY_INTEGER id ls fb pf ->
    (match fb with
    | None -> make_asn1_closed_any_INTEGER_parser id ls pf k (asn1_ls_as_parser asn1_integer_t ls)
    | Some gitems -> make_asn1_open_any_INTEGER_parser id ls gitems (make_asn1_sequence_parser (asn1_sequence_as_parser (dfst gitems))) pf k (asn1_ls_as_parser asn1_integer_t ls))

and asn1_ls_as_parser (t : eqtype) (ls : list (t * asn1_gen_items_k)) : Tot (lp : list (t & (gen_parser asn1_weak_parser_kind)) {asn1_any_t t ls == extract_types lp}) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (x, Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser (dfst y)))) :: (asn1_ls_as_parser t tl)

and asn1_lc_as_parser (lc : list (asn1_id_t & asn1_content_k)) : Tot (lp : list (asn1_id_t & (gen_parser asn1_strong_parser_kind)) {asn1_lc_t lc == extract_types lp})  (decreases lc) =
  match lc with
  | [] -> [] 
  | h :: t -> 
    let (x, y) = h in
    (x, Mkgenparser (asn1_content_t y) (parse_asn1_LC (asn1_content_as_parser y))) :: (asn1_lc_as_parser t)

and asn1_as_parser (#s : _) (k : asn1_k s) : Tot (asn1_strong_parser (asn1_t k)) (decreases k) =
  match k with
  | ASN1_ILC id k' -> parse_asn1_ILC id (asn1_content_as_parser k')
  | ASN1_CHOICE_ILC lc pf -> make_asn1_choice_parser lc pf k (asn1_lc_as_parser lc)

and asn1_as_parser_twin (#s : _) (k : asn1_k s) : Tot (asn1_strong_parser (asn1_t k) & (fp : (asn1_id_t -> asn1_strong_parser (asn1_t k)) {and_then_cases_injective fp})) (decreases k) =
  match k with
  | ASN1_ILC id k' -> 
    let p = asn1_content_as_parser k' in
    let _ = parser_asn1_ILC_twin_case_injective id p in
    (parse_asn1_ILC id p, parse_asn1_ILC_twin id p)
  | ASN1_CHOICE_ILC lc pf ->
    let lp = asn1_lc_as_parser lc in
    let _ = make_asn1_choice_parser_twin_cases_injective lc pf k lp in
    (make_asn1_choice_parser lc pf k lp, make_asn1_choice_parser_twin lc pf k lp)

and asn1_decorated_as_parser_twin (item : asn1_gen_item_k) : Tot (gp : gen_decorated_parser_twin {Mkgendcparser?.d gp == item}) =
  match item with
  | (| _, _, dk |) -> match dk with
                    | ASN1_PLAIN_ILC k -> 
                      let (p, fp) = asn1_as_parser_twin k in
                      Mkgendcparser item p fp
                    | ASN1_OPTION_ILC k -> 
                      let (p, fp) = asn1_as_parser_twin k in
                      Mkgendcparser item p fp
                    | ASN1_DEFAULT_TERMINAL id #k defv ->
                      let p = asn1_terminal_as_parser k in
                      Mkgendcparser item (parse_asn1_ILC id #(ASN1_TERMINAL k) p) (parse_asn1_ILC_twin id #(ASN1_TERMINAL k) p)
                    | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k is_valid defv ->
                      let p : asn1_weak_parser (asn1_decorated_pure_t item) = weaken _ ((asn1_terminal_as_parser k) `parse_filter` is_valid) in
                      Mkgendcparser item (parse_asn1_ILC id #(ASN1_RESTRICTED_TERMINAL k is_valid) p) (parse_asn1_ILC_twin id #(ASN1_RESTRICTED_TERMINAL k is_valid) p)

and asn1_sequence_as_parser (items : list asn1_gen_item_k) : Tot (lp : list gen_decorated_parser_twin {List.map (Mkgendcparser?.d) lp == items}) (decreases items) =
  match items with
  | [] -> []
  | hd :: tl -> (asn1_decorated_as_parser_twin hd) :: (asn1_sequence_as_parser tl)
  
