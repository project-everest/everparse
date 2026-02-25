module ASN1.Spec.Interpreter
include LowParse.Tot.Base
include LowParse.Tot.Combinators
include LowParse.Tot.List
include LowParse.Tot.Defaultable
include LowParse.Tot.Bytes

include ASN1.Debug

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
open ASN1.Spec.Set

module List = FStar.List.Tot

let parse_non_empty_list 
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t {k.parser_kind_injective == true})
: asn1_weak_parser (non_empty_list t)
= weaken _ ((parse_list p) `parse_filter` isNonEmpty)

let parse_non_empty_set 
  (#t : Type)
  (p : asn1_strong_parser t)
: asn1_weak_parser (non_empty_list t)
= (parse_asn1_set_of p) `parse_filter` isNonEmpty

let auto_asn1_sequence_t_core_equiv #id_decs (items:asn1_gen_items_l id_decs)
: Lemma
  (ensures asn1_sequence_t_core items == asn1_sequence_t (l_as_list items))
  [SMTPat (asn1_sequence_t (l_as_list items))]
= asn1_sequence_t_core_equiv items

let auto_asn1_sequence_t_core_equiv' (items:list asn1_gen_item_k)
: Lemma 
  (ensures asn1_sequence_t_core (list_as_l items) == asn1_sequence_t items)
  [SMTPat (asn1_sequence_t items)]
= asn1_sequence_t_core_equiv' items

let auto_asn1_any_t_equiv (#t:eqtype) (ls:list (t & asn1_gen_items_lk))
: Lemma
  (ensures asn1_any_t_core t ls == asn1_any_t t (t_lk_as_t_k ls))
  [SMTPat (asn1_any_t_core t ls)]
= asn1_any_t_equiv ls

let auto_asn1_any_t_equiv' (#t:eqtype) (ls:list (t & asn1_gen_items_k))
: Lemma
  (ensures asn1_any_t_core t (t_k_as_t_lk ls) == asn1_any_t t ls)
  [SMTPat (asn1_any_t t ls)]
= asn1_any_t_equiv' ls

let auto_asn1_sequence_any_t_equiv #id_decs (items : asn1_gen_items_l id_decs) (suffix_t : Type)
: Lemma
  (ensures asn1_sequence_any_t_core items suffix_t ==
           asn1_sequence_any_t (l_as_list items) suffix_t)
  [SMTPat (asn1_sequence_any_t_core items suffix_t)]
= asn1_sequence_any_t_equiv items suffix_t

let auto_asn1_sequence_any_t_equiv' (items : list asn1_gen_item_k) (suffix_t : Type)
: Lemma
  (ensures asn1_sequence_any_t_core (list_as_l items) suffix_t ==
           asn1_sequence_any_t items suffix_t)
  [SMTPat (asn1_sequence_any_t items suffix_t)]
= asn1_sequence_any_t_equiv' items suffix_t

let rec dasn1_terminal_as_parser (k : asn1_terminal_k) : asn1_weak_parser (asn1_terminal_t k)  =
  parse_debug #(asn1_terminal_t k) #(asn1_weak_parser_kind) "asn1_terminal_as_parser"
  (match k with
  | ASN1_BOOLEAN -> weaken _ parse_asn1_boolean
  | ASN1_INTEGER bound -> weaken _ (parse_untagged_bounded_integer bound)
  | ASN1_BITSTRING -> parse_asn1_bitstring
  | ASN1_OCTETSTRING -> parse_asn1_octetstring
  | ASN1_UTF8STRING -> parse_asn1_utf8string
  | ASN1_PRINTABLESTRING -> parse_asn1_printablestring
  | ASN1_IA5STRING -> parse_asn1_ia5string
  | ASN1_NULL -> parse_asn1_null
  | ASN1_OID -> parse_asn1_OIDU32
  | ASN1_UTCTIME -> parse_asn1_UTCTIME
  | ASN1_GENERALIZEDTIME -> parse_asn1_GENERALIZEDTIME
  | ASN1_PREFIXED_TERMINAL id k -> weaken asn1_weak_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k) (dasn1_terminal_as_parser k)))

and dasn1_sequence_as_parser #id_decs (ls:asn1_gen_items_l id_decs)
: Tot (lp : list gen_decorated_parser_twin {List.map (Mkgendcparser?.d) lp == l_as_list ls }) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS s d hd _ tl ->
    dasn1_decorated_as_parser_twin hd :: dasn1_sequence_as_parser tl

and dasn1_content_as_parser (k : asn1_content_k) : Tot (asn1_weak_parser (asn1_content_t k)) (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' is_valid -> weaken _ ((dasn1_terminal_as_parser k') `parse_filter` is_valid)
  | ASN1_TERMINAL k' -> dasn1_terminal_as_parser k'
  | ASN1_SEQUENCE gitems -> make_asn1_sequence_parser (dasn1_sequence_as_parser (dsnd gitems))
  | ASN1_SEQUENCE_OF k' -> parse_non_empty_list (dasn1_as_parser k')
  | ASN1_SET_OF k' -> parse_non_empty_set (dasn1_as_parser k')
  | ASN1_PREFIXED k' -> weaken _ (dasn1_as_parser k')
  | ASN1_ANY_DEFINED_BY id_decs_prefix prefix id key_k ls ofb pf pf' -> 
    let itemtwins = dasn1_sequence_as_parser prefix in //(l_as_list prefix) in
    let key_p_twin = 
      (let p = dasn1_terminal_as_parser key_k in
      let _ = parser_asn1_ILC_twin_case_injective id #(ASN1_TERMINAL key_k) p in
      Mkparsertwin #asn1_strong_parser_kind #(asn1_terminal_t key_k) (parse_asn1_ILC id #(ASN1_TERMINAL key_k) p) (parse_asn1_ILC_twin id #(ASN1_TERMINAL key_k) p))
    in
    let key_p = Mkparsertwin?.p key_p_twin in
    let key_fp = Mkparsertwin?.fp key_p_twin in
    let supported_p = dasn1_ls_as_parser (asn1_terminal_t key_k) ls in
    (match ofb with
    | None -> 
      assert_norm (asn1_weak_parser_kind `is_weaker_than` (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind));
      let suffix_p_twin = (Mkparsertwin #asn1_weak_parser_kind #(make_gen_choice_type (extract_types supported_p))
        (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser key_p supported_p))
        (let _ = make_gen_choice_weak_parser_twin_and_then_cases_injective key_fp supported_p in
         fun id -> weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin key_fp supported_p id)))
      in
      make_asn1_sequence_any_parser itemtwins suffix_p_twin
    | Some gitems -> 
      assert_norm (asn1_weak_parser_kind `is_weaker_than` (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind));
      let fallback_p = 
        Mkgenparser _
          (parse_debug "parse_any_fallback"
            (make_asn1_sequence_parser
              (dasn1_sequence_as_parser (dsnd gitems)))) in
      let suffix_p_twin = (Mkparsertwin #asn1_weak_parser_kind #(make_gen_choice_type_with_fallback (extract_types supported_p) (Mkgenparser?.t fallback_p))
        (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser key_p supported_p fallback_p))
        (let _ = make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective key_fp supported_p fallback_p in
         fun id -> weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin key_fp supported_p fallback_p id))) 
      in
      make_asn1_sequence_any_parser itemtwins suffix_p_twin) 

and dasn1_ls_as_parser (t : eqtype) (ls : list (t * asn1_gen_items_lk)) : Tot (lp : list (t & (gen_parser asn1_weak_parser_kind)) {asn1_any_t_core t ls == extract_types lp}) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (x, Mkgenparser _ (make_asn1_sequence_parser (dasn1_sequence_as_parser (dsnd y)))) :: (dasn1_ls_as_parser t tl)

and dasn1_lc_as_parser (lc : list (asn1_id_t & asn1_content_k)) : Tot (lp : list (asn1_id_t & (gen_parser asn1_strong_parser_kind)) {asn1_lc_t lc == extract_types lp})  (decreases lc) =
  match lc with
  | [] -> [] 
  | h :: t -> 
    let (x, y) = h in
    (x, Mkgenparser (asn1_content_t y) (parse_asn1_LC (dasn1_content_as_parser y))) :: (dasn1_lc_as_parser t)

and dasn1_as_parser (#s : _) (k : asn1_k s) : Tot (asn1_strong_parser (asn1_t k)) (decreases k) =
  match k with
  | ASN1_ILC id k' -> parse_debug "ASN1_ILC" (parse_asn1_ILC id (dasn1_content_as_parser k'))
  | ASN1_CHOICE_ILC lc pf -> parse_debug "ASN1_CHOICE" (make_asn1_choice_parser lc pf k (dasn1_lc_as_parser lc))
  | ASN1_ANY_ILC -> parse_debug "ASN1_ANY" (parse_asn1_anyILC)

and dasn1_as_parser_twin (#s : _) (k : asn1_k s) : Tot (asn1_strong_parser (asn1_t k) & (fp : (asn1_id_t -> asn1_strong_parser (asn1_t k)) {and_then_cases_injective fp})) (decreases k) =
  match k with
  | ASN1_ILC id k' -> 
    let p = dasn1_content_as_parser k' in
    let _ = parser_asn1_ILC_twin_case_injective id p in
    (parse_debug "ASN1_ILC" (parse_asn1_ILC id p), 
     parse_debugf "ASN1_ILC_f" (parse_asn1_ILC_twin id p))
  | ASN1_CHOICE_ILC lc pf ->
    let lp = dasn1_lc_as_parser lc in
    let _ = make_asn1_choice_parser_twin_cases_injective lc pf k lp in
    (parse_debug "ASN1_CHOICE" (make_asn1_choice_parser lc pf k lp),
     parse_debugf "ASN1_CHOICE_f" (make_asn1_choice_parser_twin lc pf k lp))
  | ASN1_ANY_ILC -> 
    let _ = parse_asn1_anyILC_twin_and_then_cases_injective () in
    (parse_debug "ASN1_ANY" (parse_asn1_anyILC), 
     parse_debugf "ASN1_ANY_f" (parse_asn1_anyILC_twin))

and dasn1_decorated_as_parser_twin 
  (#s : FStar.Set.set asn1_id_t)
  (#d : asn1_decorator)
  (dk:asn1_decorated_k s d)
: Tot (gp : gen_decorated_parser_twin {Mkgendcparser?.d gp == (| s, d, dk |) })
      (decreases dk)
= let item : asn1_gen_item_k = (| s, d, dk |) in
  match dk with
  | ASN1_PLAIN_ILC k -> 
    let (p, fp) = dasn1_as_parser_twin k in
    Mkgendcparser item p fp
  | ASN1_OPTION_ILC k -> 
    let (p, fp) = dasn1_as_parser_twin k in
    Mkgendcparser item p fp
  | ASN1_DEFAULT_TERMINAL id #k defv ->
    let p = dasn1_terminal_as_parser k in
    Mkgendcparser item (parse_asn1_ILC id #(ASN1_TERMINAL k) p) (parse_asn1_ILC_twin id #(ASN1_TERMINAL k) p)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k is_valid defv ->
    let p : asn1_weak_parser (asn1_decorated_pure_t item) = weaken _ ((dasn1_terminal_as_parser k) `parse_filter` is_valid) in
    Mkgendcparser item (parse_asn1_ILC id #(ASN1_RESTRICTED_TERMINAL k is_valid) p) (parse_asn1_ILC_twin id #(ASN1_RESTRICTED_TERMINAL k is_valid) p)


let rec asn1_terminal_as_parser (k : asn1_terminal_k) : asn1_weak_parser (asn1_terminal_t k)  =
  match k with
  | ASN1_BOOLEAN -> weaken _ parse_asn1_boolean
  | ASN1_INTEGER bound -> weaken _ (parse_untagged_bounded_integer bound)
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
  | ASN1_SEQUENCE gitems -> make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd gitems))
  | ASN1_SEQUENCE_OF k' -> parse_non_empty_list (asn1_as_parser k')
  | ASN1_SET_OF k' -> parse_non_empty_set (asn1_as_parser k')
  | ASN1_PREFIXED k' -> weaken _ (asn1_as_parser k')
  | ASN1_ANY_DEFINED_BY id_decs_prefix prefix id key_k ls ofb pf pf' -> 
    let itemtwins = asn1_sequence_as_parser prefix in
    let key_p_twin = 
      (let p = asn1_terminal_as_parser key_k in
      let _ = parser_asn1_ILC_twin_case_injective id #(ASN1_TERMINAL key_k) p in
      Mkparsertwin #asn1_strong_parser_kind #(asn1_terminal_t key_k) (parse_asn1_ILC id #(ASN1_TERMINAL key_k) p) (parse_asn1_ILC_twin id #(ASN1_TERMINAL key_k) p))
    in
    let key_p = Mkparsertwin?.p key_p_twin in
    let key_fp = Mkparsertwin?.fp key_p_twin in
    let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) ls in
    (match ofb with
    | None -> 
      assert_norm (asn1_weak_parser_kind `is_weaker_than` (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind));
      let suffix_p_twin = (Mkparsertwin #asn1_weak_parser_kind #(make_gen_choice_type (extract_types supported_p))
        (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser key_p supported_p))
        (let _ = make_gen_choice_weak_parser_twin_and_then_cases_injective key_fp supported_p in
         fun id -> weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin key_fp supported_p id)))
      in
      make_asn1_sequence_any_parser itemtwins suffix_p_twin
    | Some gitems -> 
      assert_norm (asn1_weak_parser_kind `is_weaker_than` (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind));
      let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd gitems))) in
      let suffix_p_twin = (Mkparsertwin #asn1_weak_parser_kind #(make_gen_choice_type_with_fallback (extract_types supported_p) (Mkgenparser?.t fallback_p))
        (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser key_p supported_p fallback_p))
        (let _ = make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective key_fp supported_p fallback_p in
         fun id -> weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin key_fp supported_p fallback_p id))) 
      in
      make_asn1_sequence_any_parser itemtwins suffix_p_twin) 

and asn1_ls_as_parser (t : eqtype) (ls : list (t * asn1_gen_items_lk)) : Tot (lp : list (t & (gen_parser asn1_weak_parser_kind)) {asn1_any_t_core t ls == extract_types lp}) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (x, Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd y)))) :: (asn1_ls_as_parser t tl)

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
  | ASN1_ANY_ILC -> parse_asn1_anyILC

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
  | ASN1_ANY_ILC -> 
    let _ = parse_asn1_anyILC_twin_and_then_cases_injective () in
    (parse_asn1_anyILC, parse_asn1_anyILC_twin)

and asn1_decorated_as_parser_twin #s #d (dk:asn1_decorated_k s d) 
: Tot (gp : gen_decorated_parser_twin {Mkgendcparser?.d gp == (| s, d, dk |) })
      (decreases dk)
= let item = (| s, d, dk |) in
  match dk with
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

and asn1_sequence_as_parser 
  #id_decs (ls:asn1_gen_items_l id_decs)
: Tot (lp : list gen_decorated_parser_twin {List.map (Mkgendcparser?.d) lp == l_as_list ls }) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    asn1_decorated_as_parser_twin dk :: asn1_sequence_as_parser tl
