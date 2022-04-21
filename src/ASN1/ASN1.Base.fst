module ASN1.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators

// ASN.1 Kinds

module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8
module B = FStar.Bytes
module Seq = FStar.Seq
module List = FStar.List.Tot
//module Set = FStar.Set

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

//TODO: constant tables

//ASN.1 kinds and High-level types

//Nik: Can we describe the correspondence between the kind and the type by defining a function that maps a kind to its type. In that way, we can get the parsers from the partial computation of the function on a template which is slick.

//A hack for dependency on default

type asn1_terminal_k : Type =
| ASN1_BOOLEAN
| ASN1_INTEGER
| ASN1_ENUM
| ASN1_BITSTRING
| ASN1_OCTETSTRING
| ASN1_NULL
| ASN1_OID
| ASN1_ROID
| ASN1_TIME

type asn1_boolean_t = bool

type asn1_integer_t = I32.t

//Maybe we should encode more information for enum types
type asn1_enum_t = U32.t

//Bitstring is represented as an array of bytes and 0~7 unused bits
type asn1_bitstring_t = 
| BYTES_WITH_UNUSEDBITS :
  unused : U8.t {0 <= (U8.v unused) /\ (U8.v unused) <= 7} ->
  b : B.bytes {(U8.v unused = 0) \/ 
               ((U8.v unused > 0) /\ B.length b > 0 /\ 
                FStar.UInt.mod (U8.v (B.index b ((B.length b) - 1))) (pow2 (U8.v unused)) = 0)} -> asn1_bitstring_t
//TODO: use bit op

type asn1_octetstring_t = B.bytes

type asn1_null_t = unit

//TODO
type asn1_oid_t = unit

type asn1_roid_t = unit

type asn1_time_t = unit

let asn1_terminal_t (k : asn1_terminal_k) : Type =
  match k with
  | ASN1_BOOLEAN -> asn1_boolean_t
  | ASN1_INTEGER -> asn1_integer_t
  | ASN1_ENUM -> asn1_enum_t
  | ASN1_BITSTRING -> asn1_bitstring_t
  | ASN1_OCTETSTRING -> asn1_octetstring_t
  | ASN1_NULL -> asn1_null_t
  | ASN1_OID -> asn1_oid_t
  | ASN1_ROID -> asn1_roid_t
  | ASN1_TIME -> asn1_time_t

// Those two ways of implementation should be equivalent except for a layer of wrapper which is unnecessary

(*
type asn1_terminal_t : asn1_terminal_k -> Type =
| Mk_ASN1_BOOLEAN : asn1_boolean_t -> asn1_terminal_t ASN1_BOOLEAN
| Mk_ASN1_INTEGER : asn1_integer_t -> asn1_terminal_t ASN1_INTEGER
| Mk_ASN1_ENUM : asn1_enum_t -> asn1_terminal_t ASN1_ENUM
| Mk_ASN1_BITSTRING : asn1_bitstring_t -> asn1_terminal_t ASN1_BITSTRING
| Mk_ASN1_OCTETSTRING : asn1_octetstring_t -> asn1_terminal_t ASN1_OCTETSTRING
| Mk_ASN1_NULL : asn1_terminal_t ASN1_NULL
| Mk_ASN1_OID : asn1_oid_t -> asn1_terminal_t ASN1_OID
| Mk_ASN1_ROID : asn1_roid_t -> asn1_terminal_t ASN1_ROID
| Mk_ASN1_TIME : asn1_time_t -> asn1_terminal_t ASN1_TIME

let asn1_terminal_type_of (k : asn1_terminal_k) : Type =
  match k with
  | ASN1_BOOLEAN -> asn1_terminal_t ASN1_BOOLEAN
  | ASN1_INTEGER -> asn1_terminal_t ASN1_INTEGER
  | ASN1_ENUM -> asn1_terminal_t ASN1_ENUM
  | ASN1_BITSTRING -> asn1_terminal_t ASN1_BITSTRING
  | ASN1_OCTETSTRING -> asn1_terminal_t ASN1_OCTETSTRING
  | ASN1_NULL -> asn1_terminal_t ASN1_NULL
  | ASN1_OID -> asn1_terminal_t ASN1_OID
  | ASN1_ROID -> asn1_terminal_t ASN1_ROID
  | ASN1_TIME -> asn1_terminal_t ASN1_TIME
*)

type asn1_decorator : Type =
| PLAIN
| OPTION
| DEFAULT

(*
and asn1_sequence_k : Set.set asn1_id_t -> Type =
| ASN1_SEQUENCE : items : list ((s : Set.set asn1_id_t) & (asn1_decorated_k s)) ->
                  pf : (asn1_sequence_k_wf items) ->
                  asn1_sequence_k         
| ASN1_SEQUENCE_NIL : asn1_sequence_k (Set.empty)
| ASN1_SEQUENCE_CONS_PLAIN : #s : _ -> h : asn1_k s ->
                             #s' : _ -> t : asn1_sequence_k s'->
                             asn1_sequence_k s
| ASN1_SEQUENCE_CONS_OPTIONAL : #s : _ -> h : asn1_k s ->
                                #s' : _ -> t : asn1_sequence_k s' ->
                                squash (Set.disjoint s s') ->
                                asn1_sequence_k (Set.union s s')
| ASN1_SEQUENCE_CONS_DEFAULT_TERMINAL : id : asn1_id_t ->
                                        #k : asn1_terminal_k ->
                                        defaultv : asn1_terminal_t k ->
                                        #s : _ -> t : asn1_sequence_k s ->
                                        squash (~(Set.mem id s)) ->
                                        asn1_sequence_k (Set.union (Set.singleton id) s)
*)


let rec asn1_sequence_k_wf' (li : list ((Set.set asn1_id_t) & asn1_decorator)) (s : Set.set asn1_id_t) : Type =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in
    let s'' = match d with
              | PLAIN -> Set.empty
              | OPTION | DEFAULT -> Set.union s s' in
    (Set.disjoint s s') /\ (asn1_sequence_k_wf' tl s'')
    
let asn1_sequence_k_wf (li : list ((Set.set asn1_id_t) & asn1_decorator)) : Tot Type =
  asn1_sequence_k_wf' li (Set.empty)

let my_as_set = Set.as_set

noeq noextract
type asn1_content_k : Type =
| ASN1_TERMINAL : asn1_terminal_k -> asn1_content_k
| ASN1_SEQUENCE : items : list (asn1_gen_item_k) -> 
                  pf : (asn1_sequence_k_wf (List.map (fun x -> match x with |(| s, d, _ |) -> (s, d) ) items)) ->
                  asn1_content_k
| ASN1_SEQUENCE_OF : #s : _ -> asn1_k s -> asn1_content_k
//| ASN1_SET : #s : _ -> asn1_set_k s -> asn1_content_k
| ASN1_SET_OF : #s : _ -> asn1_k s -> asn1_content_k
| ASN1_PREFIXED : #s : _ -> asn1_k s -> asn1_content_k

// The complete ASN.1 kind is indexed by the set of valid first identifiers
// Note that length does not matter here
and asn1_k : Set.set asn1_id_t -> Type =
| ASN1_ILC : id : asn1_id_t -> asn1_content_k -> asn1_k (Set.singleton id)
| ASN1_CHOICE_ILC : choices : list (asn1_id_t & asn1_content_k) -> 
                    pf : ((Cons? choices) /\ (List.noRepeats (List.map fst choices))) -> 
                    asn1_k (my_as_set (List.map fst choices))
                    
and asn1_decorated_k : Set.set asn1_id_t -> asn1_decorator -> Type =
| ASN1_PLAIN_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s PLAIN
| ASN1_OPTION_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s OPTION
| ASN1_DEFAULT_TERMINAL : id : asn1_id_t -> #k : asn1_terminal_k -> defaultv : asn1_terminal_t k -> asn1_decorated_k (Set.singleton id) DEFAULT

and asn1_gen_item_k : Type = s : Set.set asn1_id_t & d : asn1_decorator & asn1_decorated_k s d

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

let make_gen_choice_type (#key : eqtype) (lc : list (key & Type)) = (id : key) & (idlookup_t id lc)

(*
noeq noextract
type asn1_content_k : Type =
| ASN1_TERMINAL : asn1_terminal_k -> asn1_content_k
| ASN1_SEQUENCE : items : list (asn1_gen_item_k) -> 
                  pf : (asn1_sequence_k_wf (List.map (fun x -> match x with |(| s, d, _ |) -> (s, d) ) items)) ->
                  asn1_content_k
| ASN1_SEQUENCE_OF : #s : _ -> asn1_k s -> asn1_content_k
//| ASN1_SET : #s : _ -> asn1_set_k s -> asn1_content_k
| ASN1_SET_OF : #s : _ -> asn1_k s -> asn1_content_k
| ASN1_PREFIXED : #s : _ -> asn1_k s -> asn1_content_k
*)

let rec asn1_content_t (k : asn1_content_k) : Tot Type (decreases k) =
  match k with
  | ASN1_TERMINAL k' -> asn1_terminal_t k'
  | ASN1_SEQUENCE items pf -> asn1_sequence_t items
  | ASN1_SEQUENCE_OF k' -> Seq.seq (asn1_t k')
  | ASN1_SET_OF k' -> asn1_t k'
  | ASN1_PREFIXED k' -> asn1_t k'

and asn1_lc_t (lc : list (asn1_id_t & asn1_content_k)) : Tot (list (asn1_id_t & Type)) (decreases lc) =
  match lc with
  | [] -> [] 
  | h :: t -> 
    let (x, y) = h in
    (x, asn1_content_t y) :: (asn1_lc_t t)

and asn1_t (#s : _) (k : asn1_k s) : Tot Type (decreases k) =
  match k with
  | ASN1_ILC id k' -> asn1_content_t k'
  | ASN1_CHOICE_ILC lc pf -> 
    make_gen_choice_type (asn1_lc_t lc)

and asn1_decorated_t (item : asn1_gen_item_k) : Tot Type =
  match item with
  | (| _, _, dk |) -> match dk with
                    | ASN1_PLAIN_ILC k -> asn1_t k
                    | ASN1_OPTION_ILC k -> (option (asn1_t k)) 
                    | ASN1_DEFAULT_TERMINAL id defv -> (default_tv defv)

and asn1_sequence_t (items : list asn1_gen_item_k) : Tot Type (decreases items) =
  match items with
  | [] -> unit
  | [hd] -> asn1_decorated_t hd
  | hd :: tl -> 
    (asn1_decorated_t hd) & (asn1_sequence_t tl)

type asn1_length_u32_t = U32.t

let asn1_decorated_pure_t (item : asn1_gen_item_k) : Type =
  match item with
  | (| _, _, dk |) -> match dk with
                     | ASN1_PLAIN_ILC k -> asn1_t k
                     | ASN1_OPTION_ILC k -> asn1_t k
                     | ASN1_DEFAULT_TERMINAL _ #k _ -> asn1_terminal_t k 

type asn1_strong_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
}

type asn1_weak_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = None;
}

type asn1_strong_parser (t : Type) = parser asn1_strong_parser_kind t 

type asn1_weak_parser (t : Type) = parser asn1_weak_parser_kind t

noeq
type gen_parser = 
| Mkgenparser : (t : Type) -> (p : asn1_strong_parser t) -> gen_parser

noeq
type gen_decorated_parser_twin =
| Mkgendcparser : (d : asn1_gen_item_k) -> (p : asn1_strong_parser (asn1_decorated_pure_t d)) 
-> fp : (asn1_id_t -> asn1_strong_parser (asn1_decorated_pure_t d)) {and_then_cases_injective fp} ->
gen_decorated_parser_twin

(*

noeq
type gen_parser =
| Mkgenparser : (k : parser_kind) -> (t : Type) -> (p : parser k t) -> gen_parser

noeq
type gen_decorated_parser_twin =
| Mkgendcparser : (d : asn1_gen_item_k) -> (k : parser_kind) -> (p : parser k (asn1_decorated_pure_t d)) -> (k' : parser_kind) -> fp : (asn1_id_t -> parser k' (asn1_decorated_pure_t d)) {and_then_cases_injective fp} -> gen_decorated_parser_twin

*)

(*
noeq
type asn1_content_t : asn1_content_k -> Type =
| Mk_ASN1_TERMINAL : k : asn1_terminal_k -> asn1_terminal_t k -> asn1_content_t (ASN1_TERMINAL k)
| Mk_ASN1_SEQUENCE : #s : _ -> #k : asn1_sequence_k s -> asn1_content_t (ASN1_SEQUENCE k)
| Mk_ASN1_SEQUENCE_OF : #s : _ -> #k : asn1_k s -> sv : Seq.seq (asn1_t k) -> asn1_content_t (ASN1_SEQUENCE_OF k)
| MK_ASN1_SINGLETON_SET_OF : #s : _ -> #k : asn1_k s -> v : asn1_t k -> asn1_content_t (ASN1_SET_OF k)
| Mk_ASN1_PREFIXED : #s : _ -> #k : asn1_k s -> v : asn1_t k -> asn1_content_t (ASN1_PREFIXED k)

and asn1_lc_t : asn1_content_k -> Type =
| Mk_ASN1_LC : #k : _ -> asn1_content_t k -> asn1_lc_t k

and asn1_t : #s : _ -> asn1_k s -> Type =
| Mk_ASN1_ILC : id : asn1_id_t -> #k : _ -> asn1_lc_t k -> asn1_t (ASN1_ILC id k)
| Mk_ASN1_CHOICE_ILC : #s : _ -> #k : asn1_choice_k s -> asn1_choice_t k -> asn1_t (ASN1_CHOICE_ILC k)

and asn1_choice_t : #s : _ -> asn1_choice_k s -> Type =
| Mk_ASN1_CHOICE_SINGLETON : #s : _ -> #k : asn1_k s -> asn1_t k -> asn1_choice_t (ASN1_CHOICE_SINGLETON k)
| Mk_ASN1_CHOICE_CONS_THIS : #s : _ -> #k : asn1_k s -> asn1_t k -> 
                             #s' : _ -> k' : asn1_choice_k s' ->
                             #pf : squash (Set.disjoint s s') ->
                             asn1_choice_t #(Set.union s s') (ASN1_CHOICE_CONS k k' pf)
| Mk_ASN1_CHOICE_CONS_THAT : #s : _ -> k : asn1_k s ->
                             #s' : _ -> #k' : asn1_choice_k s' -> asn1_choice_t k' ->
                             #pf : squash (Set.disjoint s s') ->
                             asn1_choice_t #(Set.union s s') (ASN1_CHOICE_CONS k k' pf)

and optional_asn1_t (#s : _) (k : asn1_k s) =
| Mk_ASN1_NONE : optional_asn1_t k
| Mk_ASN1_SOME : v : (asn1_t k) -> optional_asn1_t k

and default_asn1_t (#k : asn1_terminal_k) (v : asn1_terminal_t k) =
| Mk_ASN1_DEFAULT : default_asn1_t v
| Mk_ASN1_NON_DEFAULT : v' : asn1_terminal_t k -> squash (~(v' = v)) -> default_asn1_t v 

and asn1_sequence_t : #s : _ -> asn1_sequence_k s -> Type =
| Mk_ASN1_SEQUENCE_NIL : asn1_sequence_t (ASN1_SEQUENCE_NIL)
| Mk_ASN1_SEQUENCE_CONS_PLAIN : #s : _ -> #k : asn1_k s -> h : asn1_t k ->
                                #s' : _ -> #k' : asn1_sequence_k s' -> t : asn1_sequence_t k' ->
                                asn1_sequence_t (ASN1_SEQUENCE_CONS_PLAIN k k')
| Mk_ASN1_SEQUENCE_CONS_OPTIONAL : #s : _ -> #k : asn1_k s -> h : optional_asn1_t k ->
                                   #s' : _ -> #k' : asn1_sequence_k s' -> t : asn1_sequence_t k' ->
                                   #pf : squash (Set.disjoint s s') ->
                                   asn1_sequence_t (ASN1_SEQUENCE_CONS_OPTIONAL k k' pf)
| Mk_ASN1_SEQUENCE_CONS_DEFAULT : #id : asn1_id_t -> #k : asn1_terminal_k -> #defaultv : asn1_terminal_t k -> v : default_asn1_t defaultv ->
                                  #s' : _ -> #k' : asn1_sequence_k s' -> t : asn1_sequence_t k' ->
                                  #pf : squash (~(Set.mem id s')) ->
                                  asn1_sequence_t (ASN1_SEQUENCE_CONS_DEFAULT_TERMINAL id defaultv k' pf)

*)