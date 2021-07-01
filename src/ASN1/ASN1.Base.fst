module ASN1.Base

// ASN.1 Kinds

module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8
module B = FStar.Bytes
module Seq = FStar.Seq
module Set = FStar.Set

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
| MK_ID : c : asn1_id_class_t -> f : asn1_id_flag_t -> v : asn1_id_value_t -> asn1_id_t

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
//Note: use bit op
type asn1_octetstring_t = B.bytes

type asn1_null_t = unit

(* TODO
type asn1_oid_t = unit

type asn1_roid_t = unit

type asn1_time_t = unit
*)

type asn1_terminal_t : asn1_terminal_k -> Type =
| Mk_ASN1_BOOLEAN : asn1_boolean_t -> asn1_terminal_t ASN1_BOOLEAN
| Mk_ASN1_INTEGER : asn1_integer_t -> asn1_terminal_t ASN1_INTEGER
| Mk_ASN1_ENUM : asn1_enum_t -> asn1_terminal_t ASN1_ENUM
| Mk_ASN1_BITSTRING : asn1_bitstring_t -> asn1_terminal_t ASN1_BITSTRING
| Mk_ASN1_OCTETSTRING : asn1_octetstring_t -> asn1_terminal_t ASN1_OCTETSTRING
| Mk_ASN1_NULL : asn1_terminal_t ASN1_NULL
//| Mk_ASN1_OID : asn1_oid_t -> asn1_terminal_t ASN1_OID
//| Mk_ASN1_ROID : asn1_roid_t -> asn1_terminal_t ASN1_ROID
//| Mk_ASN1_TIME : asn1_time_t -> asn1_terminal_t ASN1_TIME

noeq
type asn1_content_k : Type =
| ASN1_TERMINAL : asn1_terminal_k -> asn1_content_k
| ASN1_SEQUENCE : #s : _ -> asn1_sequence_k s -> asn1_content_k
| ASN1_SEQUENCE_OF : #s : _ -> asn1_k s -> asn1_content_k
//| ASN1_SET : #s : _ -> asn1_set_k s -> asn1_content_k
| ASN1_SET_OF : #s : _ -> asn1_k s -> asn1_content_k
| ASN1_PREFIXED : #s : _ -> asn1_k s -> asn1_content_k

// The complete ASN.1 kind is indexed by the set of valid first identifiers
// Note that length does not matter here
and asn1_k : Set.set asn1_id_t -> Type =
| ASN1_ILC : id : asn1_id_t -> asn1_content_k -> asn1_k (Set.singleton id)
| ASN1_CHOICE_ILC : #s : _ -> asn1_choice_k s -> asn1_k s

and asn1_choice_k : Set.set asn1_id_t -> Type =
| ASN1_CHOICE_SINGLETON : #s : _ -> asn1_k s -> asn1_choice_k s
| ASN1_CHOICE_CONS : #s : _ -> asn1_k s -> #s' : _ -> asn1_choice_k s' -> squash (Set.disjoint s s') -> asn1_choice_k (Set.union s s')

and asn1_sequence_k : Set.set asn1_id_t -> Type =
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


