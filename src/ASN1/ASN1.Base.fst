module ASN1.Base
open LowParse.Tot.Base
open LowParse.Tot.Combinators

open ASN1.Spec.Time
open ASN1.Spec.Content.INTEGER

// ASN.1 Kinds

module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8
module B = FStar.Bytes
module Seq = FStar.Seq
module List = FStar.List.Tot

// ASN.1 Identifier

type asn1_id_class_t =
| UNIVERSAL
| APPLICATION
| CONTEXT_SPECIFIC
| PRIVATE

type asn1_id_flag_t = 
| PRIMITIVE
| CONSTRUCTED

type asn1_id_value_t = U32.t

type asn1_id_t =
| MK_ASN1_ID : c : asn1_id_class_t -> f : asn1_id_flag_t -> v : asn1_id_value_t -> asn1_id_t

//TODO: constant tables (Currently in X.509)

//ASN.1 kinds and High-level types

//Can we describe the correspondence between the kind and the type by defining a function that maps a kind to its type. In that way, we can get the parsers from the partial computation of the function on a template which is slick.

//A hack for dependency on default

type asn1_terminal_k : Type =
| ASN1_BOOLEAN
| ASN1_INTEGER : (bound : pos) -> asn1_terminal_k
// | ASN1_ENUM
| ASN1_BITSTRING
| ASN1_OCTETSTRING
| ASN1_PRINTABLESTRING
| ASN1_UTF8STRING
| ASN1_IA5STRING
| ASN1_NULL
| ASN1_OID
// | ASN1_ROID
| ASN1_UTCTIME
| ASN1_GENERALIZEDTIME
| ASN1_PREFIXED_TERMINAL : asn1_id_t -> asn1_terminal_k -> asn1_terminal_k

type asn1_boolean_t = bool

type asn1_integer_t (bound : pos) = integer_in_interval bound

let rec pow2_mono (n m:nat)
: Lemma
  (requires n < m)
  (ensures pow2 n < pow2 m)
= if n + 1 = m then () else pow2_mono n (m - 1)
let pow2_le (n:nat {n < 8}) : Lemma (pow2 n < 256) = pow2_mono n 8

//Bitstring is represented as an array of bytes and 0~7 unused bits
type asn1_bitstring_t = 
| BYTES_WITH_UNUSEDBITS :
  unused : U8.t {0 <= (U8.v unused) /\ (U8.v unused) <= 7} ->
  b : B.bytes {let _ = pow2_le (U8.v unused) in
               (U8.v unused = 0) \/ 
               ((U8.v unused > 0) /\ B.length b > 0 /\ 
                FStar.UInt.mod (U8.v (B.index b ((B.length b) - 1))) (pow2 (U8.v unused)) = 0)} -> asn1_bitstring_t
//TODO: use bit op

type asn1_octetstring_t = B.bytes

type utf8_cp_t = (x : U32.t {U32.v x < pow2 21})

type asn1_utf8string_t = list utf8_cp_t

let is_printable_char (ch : U8.t) : bool =
  let v = U8.v ch in
  (65 <= v && v <= 90) ||  // A - Z
  (97 <= v && v <= 122) || // a - z
  (48 <= v && v <= 57) ||  // 0 - 9
  v = 32 ||              // (space)
  (39 <= v && v <= 41) ||  // '()
  (43 <= v && v <= 47) ||  // +,-./
  v = 58 || v = 61 || v = 63 // :=?

type asn1_printablestring_t = list (b : byte {is_printable_char b})

let is_ia5_char (ch : U8.t) : bool = U8.v ch < 128

type asn1_ia5string_t = list (b : byte {is_ia5_char b})

type asn1_null_t = unit

let asn1_OID_wf' (value1 value2 : U32.t) =
  (U32.v value1 < 2 && U32.v value2 < 40) || (U32.v value1 = 2 && U32.v value2 < 256 - 80)

let asn1_OID_wf (l : list U32.t) =
  List.length l >= 2 &&
  (match l with
  | value1 :: value2 :: tl -> asn1_OID_wf' value1 value2)

type asn1_oid_t = 
  (l : list U32.t {asn1_OID_wf l})

// type asn1_roid_t = unit

type asn1_utctime_t = (b : B.bytes {is_valid_ASN1UTCTIME b})

type asn1_generalizedtime_t = (b : B.bytes {is_valid_ASN1GENERALIZEDTIME b})

let rec asn1_terminal_t (k : asn1_terminal_k) : eqtype =
  match k with
  | ASN1_BOOLEAN -> asn1_boolean_t
  | ASN1_INTEGER bound -> asn1_integer_t bound
//  | ASN1_ENUM -> asn1_enum_t
  | ASN1_BITSTRING -> asn1_bitstring_t
  | ASN1_OCTETSTRING -> asn1_octetstring_t
  | ASN1_UTF8STRING -> asn1_utf8string_t
  | ASN1_PRINTABLESTRING -> asn1_printablestring_t
  | ASN1_IA5STRING -> asn1_ia5string_t
  | ASN1_NULL -> asn1_null_t
  | ASN1_OID -> asn1_oid_t
//  | ASN1_ROID -> asn1_roid_t
  | ASN1_UTCTIME -> asn1_utctime_t
  | ASN1_GENERALIZEDTIME -> asn1_generalizedtime_t
  | ASN1_PREFIXED_TERMINAL _ k -> asn1_terminal_t k

type asn1_decorator : Type =
| PLAIN
| OPTION
| DEFAULT

let id_dec = Set.set asn1_id_t & asn1_decorator
let id_decs = list id_dec

let rec asn1_sequence_k_wf' (li : id_decs) (s : Set.set asn1_id_t) : Type =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in
    Set.disjoint s s' /\
    (match d with
    | PLAIN -> asn1_sequence_k_wf tl
    | _ -> asn1_sequence_k_wf' tl (Set.union s s'))

and asn1_sequence_k_wf (li : id_decs) : Type =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in 
    match d with
    | PLAIN -> asn1_sequence_k_wf tl
    | OPTION | DEFAULT -> asn1_sequence_k_wf' tl s'

let my_as_set l = Set.as_set l

let proj2_of_3 (#a #b : Type) (#c : a -> b -> Type) (x : dtuple3 a (fun _ -> b) c) : a * b = 
  let (| xa, xb, _ |) = x in (xa, xb)

let rec asn1_any_prefix_k_wf' (ks : Set.set asn1_id_t) (li : id_decs) (s : Set.set asn1_id_t) : Type =
  match li with
  | [] -> Set.disjoint s ks
  | hd :: tl ->
    let (s', d) = hd in
    Set.disjoint s s' /\
    (match d with
    | PLAIN -> asn1_any_prefix_k_wf ks tl
    | OPTION | DEFAULT -> asn1_any_prefix_k_wf' ks tl (Set.union s s'))

and asn1_any_prefix_k_wf (ks : Set.set asn1_id_t) (li : id_decs) : Type =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in 
    match d with
    | PLAIN -> asn1_any_prefix_k_wf ks tl
    | OPTION | DEFAULT -> asn1_any_prefix_k_wf' ks tl s'

noeq //noextract
type asn1_content_k : Type =
| ASN1_RESTRICTED_TERMINAL : (k : asn1_terminal_k) -> (is_valid : (asn1_terminal_t k) -> bool) -> asn1_content_k
| ASN1_TERMINAL : asn1_terminal_k -> asn1_content_k
| ASN1_SEQUENCE : asn1_gen_items_lk -> asn1_content_k
| ASN1_SEQUENCE_OF : #s : _ -> asn1_k s -> asn1_content_k
//| ASN1_SET : #s : _ -> asn1_set_k s -> asn1_content_k
| ASN1_SET_OF : #s : _ -> asn1_k s -> asn1_content_k
| ASN1_PREFIXED : #s : _ -> asn1_k s -> asn1_content_k
| ASN1_ANY_DEFINED_BY :
             id_decs_prefix : id_decs ->
             prefix:asn1_gen_items_l id_decs_prefix ->
             id : asn1_id_t ->
             key_k : asn1_terminal_k ->
             supported : list (asn1_terminal_t key_k * asn1_gen_items_lk) -> 
             fallback : option asn1_gen_items_lk ->
             pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton id) id_decs_prefix) ->
             pf_sup : squash (List.noRepeats (List.map fst supported)) -> 
             asn1_content_k

// The complete ASN.1 kind is indexed by the set of valid first identifiers
// Note that length does not matter here
and asn1_k : Set.set asn1_id_t -> Type =
| ASN1_ILC : id : asn1_id_t -> asn1_content_k -> asn1_k (Set.singleton id)
| ASN1_CHOICE_ILC : choices : list (asn1_id_t & asn1_content_k) -> 
                    pf : squash (List.noRepeats (List.map fst choices)) -> 
                    asn1_k (my_as_set (List.map fst choices))
| ASN1_ANY_ILC : asn1_k (Set.complement (Set.empty))                   
                    
and asn1_decorated_k : Set.set asn1_id_t -> asn1_decorator -> Type =
| ASN1_PLAIN_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s PLAIN
| ASN1_OPTION_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s OPTION
| ASN1_DEFAULT_TERMINAL : id : asn1_id_t -> #k : asn1_terminal_k -> defaultv : asn1_terminal_t k -> asn1_decorated_k (Set.singleton id) DEFAULT
| ASN1_DEFAULT_RESTRICTED_TERMINAL : id : asn1_id_t -> #k : asn1_terminal_k -> is_valid : ((asn1_terminal_t k) -> bool) -> 
                                     defaultv : asn1_terminal_t k {is_valid defaultv = true} -> asn1_decorated_k (Set.singleton id) DEFAULT


and asn1_gen_items_l : id_decs -> Type0 = 
  | ASN1_GEN_ITEMS_NIL : asn1_gen_items_l []
  | ASN1_GEN_ITEMS_CONS : s:Set.set asn1_id_t -> d:asn1_decorator -> asn1_decorated_k s d -> 
                          tl:id_decs -> asn1_gen_items_l tl -> asn1_gen_items_l ((s, d)::tl)

and asn1_gen_items_lk : Type = (id_decs:id_decs { asn1_sequence_k_wf id_decs } & asn1_gen_items_l id_decs)


let asn1_gen_item_k : Type = s : Set.set asn1_id_t & d : asn1_decorator & asn1_decorated_k s d

let asn1_gen_items_k : Type = items : list (asn1_gen_item_k) & squash (asn1_sequence_k_wf (List.map proj2_of_3 items))


let mk_ASN1_GEN_ITEM (#s) (#d) (k : asn1_decorated_k s d) : asn1_gen_item_k =
  (| s, d, k |)

(* Conversions to go between asn1_gen_items_lk and asn1_get_items_k *)
let rec l_as_list (#i:id_decs) (l:asn1_gen_items_l i)
  : r:list asn1_gen_item_k { List.map proj2_of_3 r == i }
  = match l with
    | ASN1_GEN_ITEMS_NIL -> []
    | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
      (| s, d, dd |) :: l_as_list tl

let lk_as_k (lk:asn1_gen_items_lk)
  : asn1_gen_items_k
  = let (| ids, l |) = lk in
    (| l_as_list l, () |)

let rec list_as_l (l:list asn1_gen_item_k)
  : asn1_gen_items_l (List.map proj2_of_3 l)
  = match l with
    | [] -> ASN1_GEN_ITEMS_NIL
    | hd::tl ->
      let (| i, d, dd |) = hd in
      ASN1_GEN_ITEMS_CONS i d dd _ (list_as_l tl)

let k_as_lk (k:asn1_gen_items_k)
  : asn1_gen_items_lk
  = let (| l, _ |) = k in
    (| _, list_as_l l |)

type default_tv (#a : eqtype) (v : a) =
| Default : default_tv v
| Nondefault  : v' : a{~(v' = v)} -> default_tv v

let v_of_default (#a : eqtype) (#v : a) (v' : default_tv v) : a =
  match v' with
  | Default -> v
  | Nondefault v'' -> v''

let rec assoc_slt (#xT: eqtype) (#yT : Type) (l : list (xT & yT)) (x : xT) :
  Lemma (requires Some? (List.assoc x l))
        (ensures (let Some y = (List.assoc x l) in y << l))
        (decreases l)
= match l with
  | (a, b) :: t -> if x = a then () else (assoc_slt t x)

let idlookup_t_postcond (#key : eqtype) (id : key) (lc : list (key & Type)) (t : Type) : GTot Type0
= (t << lc \/ t == False)

let idlookup_t (#key : eqtype) (id : key) (lc : list (key & Type)) :
  Pure Type
  (requires True)
  (ensures fun t -> idlookup_t_postcond id lc t)
= let _ = List.assoc_mem id lc in
  let res = List.assoc id lc in
  match res with
  | Some t -> 
    let _ = List.assoc_memP_some id t lc in
    let _ = assoc_slt lc id in
    t  
  | None -> 
    let _ = List.assoc_memP_none id lc in
    False 

let idlookup_with_fallback_t_postcond (#key : eqtype) (id : key) (lc : list (key & Type)) (fb : Type) (t : Type) : GTot Type0
= (t << lc \/ t == fb)

let idlookup_with_fallback_t (#key : eqtype) (id : key) (lc : list (key & Type)) (fb : Type) :
  Pure Type
  (requires True)
  (ensures fun t -> idlookup_with_fallback_t_postcond id lc fb t)
= let _ = List.assoc_mem id lc in
  let res = List.assoc id lc in
  match res with
  | Some t -> 
    let _ = List.assoc_memP_some id t lc in
    let _ = assoc_slt lc id in
    t  
  | None -> 
    let _ = List.assoc_memP_none id lc in
    fb

let make_gen_choice_type (#key : eqtype) (lc : list (key & Type)) = id : key & idlookup_t id lc

let make_gen_choice_type_with_fallback (#key : eqtype) (lc : list (key & Type)) (fb : Type) = id : key & idlookup_with_fallback_t id lc fb

let isNonEmpty (#t : Type) (l : list t)
= match l with
  | [] -> false
  | _ -> true

let non_empty_list (t : Type) = l : (list t) {isNonEmpty l}

let rec asn1_content_t (k : asn1_content_k) : Tot Type (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' is_valid -> parse_filter_refine is_valid
  | ASN1_TERMINAL k' -> asn1_terminal_t k'
  | ASN1_SEQUENCE gitems -> asn1_sequence_t_core (dsnd gitems)
  | ASN1_SEQUENCE_OF k' ->  non_empty_list (asn1_t k')
  | ASN1_SET_OF k' -> non_empty_list (asn1_t k') 
  | ASN1_PREFIXED k' -> asn1_t k'
  | ASN1_ANY_DEFINED_BY id_decs_prefix prefix id key_k ls ofb pf_wf pf_sup -> 
    let suffix_t =
      (match ofb with
      | None -> make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) ls)
      | Some fb -> make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) ls) (asn1_sequence_t_core (dsnd fb))) in
    asn1_sequence_any_t_core prefix suffix_t

and asn1_any_t_core (t : eqtype) (ls : list (t * asn1_gen_items_lk)) : Tot (list (t & Type)) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (x, asn1_sequence_t_core (dsnd y)) :: asn1_any_t_core t tl

and asn1_lc_t (lc : list (asn1_id_t & asn1_content_k)) : Tot (list (asn1_id_t & Type)) (decreases lc) =
  match lc with
  | [] -> [] 
  | h :: t -> 
    let (x, y) = h in
    (x, asn1_content_t y) :: (asn1_lc_t t)

and asn1_t (#s : _) (k : asn1_k s) : Tot Type (decreases k) =
  match k with
  | ASN1_ILC id k' -> asn1_content_t k'
  | ASN1_CHOICE_ILC lc pf -> make_gen_choice_type (asn1_lc_t lc)
  | ASN1_ANY_ILC -> asn1_id_t & asn1_octetstring_t

and asn1_decorated_t_core #s #d (dk:asn1_decorated_k s d) : Tot Type  (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> asn1_t k
  | ASN1_OPTION_ILC k -> option (asn1_t k)
  | ASN1_DEFAULT_TERMINAL id defv -> default_tv defv
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k is_valid defv -> default_tv #(parse_filter_refine is_valid) defv

and asn1_sequence_t_core #id_decs (items:asn1_gen_items_l id_decs) : Tot Type (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> unit
  | ASN1_GEN_ITEMS_CONS s d dd _ ASN1_GEN_ITEMS_NIL ->
    asn1_decorated_t_core dd
  | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
    asn1_decorated_t_core dd & asn1_sequence_t_core tl

and asn1_sequence_any_t_core #id_decs (items : asn1_gen_items_l id_decs) (suffix_t : Type) : Tot Type (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> suffix_t
  | ASN1_GEN_ITEMS_CONS s d dd _ ASN1_GEN_ITEMS_NIL ->
    asn1_decorated_t_core dd & suffix_t
  | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
    asn1_decorated_t_core dd & asn1_sequence_any_t_core tl suffix_t

(* It may be convenient to use these alternative but equivalent formulations in the rest of the development *)
let asn1_decorated_t (i:asn1_gen_item_k) : Type =
  let (| _, _, dk |) = i in
  asn1_decorated_t_core dk

let rec asn1_sequence_t (items:list asn1_gen_item_k) =
  match items with
  | [] -> unit
  | [hd] ->
    asn1_decorated_t hd
  | hd::tl -> 
    asn1_decorated_t hd & asn1_sequence_t tl

let rec asn1_sequence_t_core_equiv #id_decs (items:asn1_gen_items_l id_decs)
  : Lemma (ensures asn1_sequence_t_core items == asn1_sequence_t (l_as_list items))
          (decreases items)
  = match items with
    | ASN1_GEN_ITEMS_NIL -> ()
    | ASN1_GEN_ITEMS_CONS _ _ _ _ tl ->
      asn1_sequence_t_core_equiv tl

let rec asn1_sequence_t_core_equiv' (items:list asn1_gen_item_k)
  : Lemma (ensures asn1_sequence_t_core (list_as_l items) == asn1_sequence_t items)
          (decreases items)
  = match items with
    | [] -> ()
    | hd::tl -> asn1_sequence_t_core_equiv' tl


let rec asn1_any_t (t : eqtype) (ls : list (t * asn1_gen_items_k)) : Tot (list (t & Type)) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (x, asn1_sequence_t (dfst y)) :: asn1_any_t _ tl

let t_lk_as_t_k #t (ls:list (t & asn1_gen_items_lk))
  : list (t & asn1_gen_items_k)
  = List.map (fun (t, lk) -> t, lk_as_k lk) ls

let t_k_as_t_lk #t (ls:list (t & asn1_gen_items_k))
  : list (t & asn1_gen_items_lk)
  = List.map (fun (t, k) -> t, k_as_lk k) ls

let rec asn1_any_t_equiv (#t:eqtype) (ls:list (t & asn1_gen_items_lk))
  : Lemma (ensures asn1_any_t_core t ls == asn1_any_t t (t_lk_as_t_k ls))
   = match ls with
     | [] -> ()
     | hd::tl ->
       let x,y = hd in
       asn1_any_t_equiv tl; asn1_sequence_t_core_equiv (dsnd y)

let rec asn1_any_t_equiv' (#t:eqtype) (ls:list (t & asn1_gen_items_k))
  : Lemma (ensures asn1_any_t_core t (t_k_as_t_lk ls) == asn1_any_t t ls)
   = match ls with
     | [] -> ()
     | hd::tl ->
       let x,y = hd in
       asn1_any_t_equiv' tl; asn1_sequence_t_core_equiv' (dfst y)


let rec asn1_sequence_any_t (items : list asn1_gen_item_k) (suffix_t : Type) : Tot Type (decreases items) =
  match items with
  | [] -> suffix_t
  | [hd] -> asn1_decorated_t hd & suffix_t
  | hd :: tl ->
    asn1_decorated_t hd & asn1_sequence_any_t tl suffix_t

let rec asn1_sequence_any_t_equiv #id_decs (items : asn1_gen_items_l id_decs) (suffix_t : Type)
  : Lemma (ensures asn1_sequence_any_t_core items suffix_t ==
                   asn1_sequence_any_t (l_as_list items) suffix_t)
          (decreases items)
  = match items with
    | ASN1_GEN_ITEMS_NIL -> ()
    | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
      asn1_sequence_any_t_equiv tl suffix_t


let rec asn1_sequence_any_t_equiv' (items : list asn1_gen_item_k) (suffix_t : Type)
  : Lemma (ensures asn1_sequence_any_t_core (list_as_l items) suffix_t ==
                   asn1_sequence_any_t items suffix_t)
          (decreases items)
  = match items with
    | [] -> ()
    | hd::tl -> asn1_sequence_any_t_equiv' tl suffix_t

type asn1_length_u32_t = U32.t

let asn1_decorated_pure_t (item : asn1_gen_item_k) : Type =
  match item with
  | (| _, _, dk |) -> match dk with
                     | ASN1_PLAIN_ILC k -> asn1_t k
                     | ASN1_OPTION_ILC k -> asn1_t k
                     | ASN1_DEFAULT_TERMINAL _ #k _ -> asn1_terminal_t k 
                     | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k is_valid _ -> parse_filter_refine is_valid

type asn1_strong_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_injective = true;
}

type asn1_weak_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = None;
  parser_kind_injective = true;
}

type asn1_strong_parser (t : Type) = parser asn1_strong_parser_kind t 

type asn1_weak_parser (t : Type) = parser asn1_weak_parser_kind t

noeq
type gen_parser (k : parser_kind) = 
| Mkgenparser : (t : Type) -> (p : parser k t) -> gen_parser k

noeq
type parser_twin (k : parser_kind) (t : Type) =
| Mkparsertwin : (p : parser k t) -> (fp : (asn1_id_t -> parser k t) {and_then_cases_injective fp} ) -> parser_twin k t

noeq
type gen_decorated_parser_twin =
| Mkgendcparser : (d : asn1_gen_item_k) -> (p : asn1_strong_parser (asn1_decorated_pure_t d)) 
-> fp : (asn1_id_t -> asn1_strong_parser (asn1_decorated_pure_t d)) {and_then_cases_injective fp} ->
gen_decorated_parser_twin
