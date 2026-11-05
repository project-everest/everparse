module ASN1.Pulse.Rel
#lang-pulse

(* Pulse representations of ASN.1 DER values (`asn1_impl_t k`), and their
   relation with the typed spec values (`asn1_rel k pm impl x`).

   Byte-carrying leaves are slices related to the spec value by the
   ENCODING-EQUALITY relation `prel_slice_ser enc` (the slice holds exactly
   the content encoding of the value). Repetitions (SEQUENCE OF, SET OF)
   are mixed lists (`LowParse.PulseParse.Iterator`), with `U32.t` counts.

   The relation is indexed by a permission `pm`, which is the fraction of
   every slice, reference and mixed list cell reachable from the value: as
   parsed values borrow the input buffer, this is the fraction of the input
   buffer they hold. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module I64 = FStar.Int64
module IO = LowParse.PulseParse.Iterator.IntOps
module It = LowParse.PulseParse.Iterator
module ItT = LowParse.PulseParse.Iterator.Type
module SB = LowParse.Spec.Base
module Ser = ASN1.Spec.Serializer
module Conf = ASN1.Spec.Conformance

(* Permission-indexed relations and their combinators *)

let prel (t: Type0) (u: Type) = perm -> t -> u -> slprop

let prel_eq (t: eqtype) (_: perm) (x y: t) : slprop = pure (x == y)

let prel_slice_ser (#u: Type) (enc: u -> GTot SB.bytes) (pm: perm) (s: S.slice U8.t) (x: u) : slprop =
  exists* w . S.pts_to s #pm w ** pure (w == enc x)

let prel_pair (#t1 #t2: Type0) (#u1 #u2: Type) (r1: prel t1 u1) (r2: prel t2 u2) (pm: perm) (x: t1 & t2) (y: u1 & u2) : slprop =
  r1 pm (fst x) (fst y) ** r2 pm (snd x) (snd y)

let prel_option (#t: Type0) (#u: Type) (r: prel t u) (pm: perm) (x: option t) (y: option u) : slprop =
  match x, y with
  | None, None -> emp
  | Some x', Some y' -> r pm x' y'
  | _ -> pure False

let prel_pair_eq (#t1 #t2: Type0) (#u1 #u2: Type) (r1: prel t1 u1) (r2: prel t2 u2) pm x1 x2 y1 y2
: Lemma (prel_pair r1 r2 pm (x1, x2) (y1, y2) == (r1 pm x1 y1 ** r2 pm x2 y2))
= ()

(* Leaf representations *)

let fits_i64 (x: int) : bool = -9223372036854775808 <= x && x < 9223372036854775808

noeq
type asn1_int_impl =
| Small : I64.t -> asn1_int_impl
| Big : S.slice U8.t -> asn1_int_impl

noeq
type asn1_bitstring_impl = {
  unused: U8.t;
  bytes: S.slice U8.t;
}

let prel_emp (t: Type0) (u: Type) (_: perm) (_: t) (_: u) : slprop = emp

let asn1_small_int_rel (bound: pos) (_: perm) (x: I64.t) (y: asn1_integer_t bound) : slprop = pure (I64.v x == y)

(* INTEGER contents of at most 8 octets always fit in 64 bits *)
inline_for_extraction
let small_integer (bound: pos) : bool = bound <= 8

(* The representation type of a bounded INTEGER. It matches on the bound
   directly, rather than branching on `small_integer bound`: Custard computes
   a type-level function applied to a schema with Beta, Iota and Zeta only,
   so neither primitive comparisons nor a function call in the scrutinee
   would reduce. *)
let integer_impl_t (bound: pos) : Type0 =
  match bound with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 -> I64.t
  | _ -> asn1_int_impl

let integer_impl_t_eq (bound: pos)
: Lemma (integer_impl_t bound == (if small_integer bound then I64.t else asn1_int_impl))
  [SMTPat (integer_impl_t bound)]
= ()

let asn1_int_rel (bound: pos) (pm: perm) (x: asn1_int_impl) (y: asn1_integer_t bound) : slprop =
  match x with
  | Small i -> pure (I64.v i == y)
  | Big s -> prel_slice_ser (integer_enc bound) pm s y ** pure (~ (fits_i64 y))

let asn1_bitstring_rel (pm: perm) (x: asn1_bitstring_impl) (y: asn1_bitstring_t) : slprop =
  exists* w . S.pts_to x.bytes #pm w ** pure (x.unused == BYTES_WITH_UNUSEDBITS?.unused y /\ w == BYTES_WITH_UNUSEDBITS?.b y)

let rec asn1_terminal_impl_t (k: asn1_terminal_k) : Tot Type0 (decreases k) =
  match k with
  | ASN1_BOOLEAN -> bool
  | ASN1_NULL -> unit
  | ASN1_INTEGER bound -> integer_impl_t bound
  | ASN1_BITSTRING -> asn1_bitstring_impl
  | ASN1_PREFIXED_TERMINAL _ k' -> asn1_terminal_impl_t k'
  | ASN1_OCTETSTRING
  | ASN1_PRINTABLESTRING
  | ASN1_UTF8STRING
  | ASN1_IA5STRING
  | ASN1_VISIBLESTRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_TELETEXSTRING
  | ASN1_NUMERICSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_OID
  | ASN1_RELATIVE_OID
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME -> S.slice U8.t

let rec asn1_terminal_rel (k: asn1_terminal_k) : Tot (prel (asn1_terminal_impl_t k) (asn1_terminal_t k)) (decreases k) =
  match k returns prel (asn1_terminal_impl_t k) (asn1_terminal_t k) with
  | ASN1_BOOLEAN -> prel_eq bool
  | ASN1_NULL -> prel_emp unit unit
  | ASN1_INTEGER bound ->
    if small_integer bound
    then asn1_small_int_rel bound
    else asn1_int_rel bound
  | ASN1_BITSTRING -> asn1_bitstring_rel
  | ASN1_PREFIXED_TERMINAL _ k' -> asn1_terminal_rel k'
  | ASN1_OCTETSTRING -> prel_slice_ser (leaf_enc ASN1_OCTETSTRING)
  | ASN1_PRINTABLESTRING -> prel_slice_ser (leaf_enc ASN1_PRINTABLESTRING)
  | ASN1_UTF8STRING -> prel_slice_ser (leaf_enc ASN1_UTF8STRING)
  | ASN1_IA5STRING -> prel_slice_ser (leaf_enc ASN1_IA5STRING)
  | ASN1_VISIBLESTRING -> prel_slice_ser (leaf_enc ASN1_VISIBLESTRING)
  | ASN1_BMPSTRING -> prel_slice_ser (leaf_enc ASN1_BMPSTRING)
  | ASN1_UNIVERSALSTRING -> prel_slice_ser (leaf_enc ASN1_UNIVERSALSTRING)
  | ASN1_TELETEXSTRING -> prel_slice_ser (leaf_enc ASN1_TELETEXSTRING)
  | ASN1_NUMERICSTRING -> prel_slice_ser (leaf_enc ASN1_NUMERICSTRING)
  | ASN1_VIDEOTEXSTRING -> prel_slice_ser (leaf_enc ASN1_VIDEOTEXSTRING)
  | ASN1_GRAPHICSTRING -> prel_slice_ser (leaf_enc ASN1_GRAPHICSTRING)
  | ASN1_GENERALSTRING -> prel_slice_ser (leaf_enc ASN1_GENERALSTRING)
  | ASN1_OBJECTDESCRIPTOR -> prel_slice_ser (leaf_enc ASN1_OBJECTDESCRIPTOR)
  | ASN1_OID -> prel_slice_ser (leaf_enc ASN1_OID)
  | ASN1_RELATIVE_OID -> prel_slice_ser (leaf_enc ASN1_RELATIVE_OID)
  | ASN1_OID_IRI -> prel_slice_ser (leaf_enc ASN1_OID_IRI)
  | ASN1_RELATIVE_OID_IRI -> prel_slice_ser (leaf_enc ASN1_RELATIVE_OID_IRI)
  | ASN1_UTCTIME -> prel_slice_ser (leaf_enc ASN1_UTCTIME)
  | ASN1_GENERALIZEDTIME -> prel_slice_ser (leaf_enc ASN1_GENERALIZEDTIME)
  | ASN1_DATE -> prel_slice_ser (leaf_enc ASN1_DATE)
  | ASN1_TIME_OF_DAY -> prel_slice_ser (leaf_enc ASN1_TIME_OF_DAY)
  | ASN1_DATE_TIME -> prel_slice_ser (leaf_enc ASN1_DATE_TIME)

(* Constructed representations, mirroring `asn1_t`:
   - SEQUENCE, SET: nested pairs, as `asn1_sequence_t_core`
   - OPTIONAL, DEFAULT: `option` (`None` for absent / the default value)
   - CHOICE: right-nested `either`, the position encoding the alternative
   - SEQUENCE OF, SET OF: mixed lists with `size_t` counts (a content parser
     knows its input length fits `size_t`, and there are at most that many
     elements; nothing bounds it by 2^32 at that level)
   - ANY: the raw TLV encoding, as a slice
   - ANY DEFINED BY: the prefix items, then a right-nested `either` over the
     supported keys (the key is implied by the position), then, if any, the
     fallback (key and items). *)

inline_for_extraction
let ml_ops = IO.sizet_ops

let ml (t: Type0) : Type0 = ItT.mixed_list SZ.t t

(* NOTE: the impl types use the projector `Mkdtuple2?._2` rather than `dsnd`:
   Custard reduces a type-level function by unfolding only that function, and
   a projector applied to a constructor reduces by iota, whereas `dsnd` would
   stay stuck and the type would extract as `any`. *)
let rec asn1_content_impl_t (k: asn1_content_k) : Tot Type0 (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> asn1_terminal_impl_t k'
  | ASN1_TERMINAL k' -> asn1_terminal_impl_t k'
  | ASN1_SEQUENCE gitems -> asn1_items_impl_t (Mkdtuple2?._2 gitems)
  | ASN1_SET _ items _ -> asn1_items_impl_t items
  | ASN1_SEQUENCE_OF _ k' -> ml (asn1_impl_t k')
  | ASN1_SET_OF _ k' -> ml (asn1_impl_t k')
  | ASN1_PREFIXED k' -> asn1_impl_t k'
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    (* Custard reduces only the head type function, so the fallback type is
       computed here, and `asn1_adb_suffix_impl_t` always receives a literal
       `None` or `Some` *)
    begin match ofb with
    | None -> asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None)
    | Some fb -> asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb))))
    end

and asn1_adb_suffix_impl_t (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fbt: option Type0) : Tot Type0 (decreases ls) =
  match ls with
  | [] ->
    begin match fbt with
    | None -> unit
    | Some t -> t
    end
  | [(_, it)] ->
    begin match fbt with
    | None -> asn1_items_impl_t (Mkdtuple2?._2 it)
    | Some t -> either (asn1_items_impl_t (Mkdtuple2?._2 it)) t
    end
  | (_, it) :: tl -> either (asn1_items_impl_t (Mkdtuple2?._2 it)) (asn1_adb_suffix_impl_t key_k tl fbt)

and asn1_lc_impl_t (lc: list (asn1_id_t & asn1_content_k)) : Tot Type0 (decreases lc) =
  match lc with
  | [] -> unit
  | [(_, c)] -> asn1_content_impl_t c
  | (_, c) :: tl -> either (asn1_content_impl_t c) (asn1_lc_impl_t tl)

and asn1_impl_t (#s: _) (k: asn1_k s) : Tot Type0 (decreases k) =
  match k with
  | ASN1_ILC _ k' -> asn1_content_impl_t k'
  | ASN1_CHOICE_ILC lc _ -> asn1_lc_impl_t lc
  | ASN1_ANY_ILC -> S.slice U8.t

and asn1_decorated_impl_t (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot Type0 (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> asn1_impl_t k
  | ASN1_OPTION_ILC k -> option (asn1_impl_t k)
  | ASN1_DEFAULT_TERMINAL _ #k _ -> option (asn1_terminal_impl_t k)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k _ _ -> option (asn1_terminal_impl_t k)

and asn1_items_impl_t (#ids: _) (items: asn1_gen_items_l ids) : Tot Type0 (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> unit
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> asn1_decorated_impl_t dk
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> asn1_decorated_impl_t dk & asn1_items_impl_t tl

and asn1_items_any_impl_t (#ids: _) (items: asn1_gen_items_l ids) (sfx: Type0) : Tot Type0 (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfx
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> asn1_decorated_impl_t dk & sfx
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> asn1_decorated_impl_t dk & asn1_items_any_impl_t tl sfx

(* Impl descriptors: the choice of Pulse representation types for a schema.

   A descriptor `adesc k t` mirrors the schema `k` and fixes `t`, the Pulse
   type of its values. Structural nodes compute their type from their
   children's as above (nested pairs for items, right-nested `either` for
   CHOICE alternatives and ANY DEFINED BY keys, `option` for
   OPTIONAL/DEFAULT, mixed lists for SEQUENCE OF/SET OF), and a VIEW node
   (`D_VIEW`, `CD_VIEW`, `DD_VIEW`) replaces the type of a node by any type
   `ty`, with a shallow view `view: ty -> t` and a constructor `mk: t -> ty`
   such that `view (mk x) == x`: e.g. a named struct for a SEQUENCE, or a
   named case type for a CHOICE. As views are shallow, neither parsers nor
   writers ever convert a value deeply.

   The impl type is an index, rather than computed by a type-level function
   of the descriptor, so Custard never needs to reduce a type function
   applied to a descriptor, and a root can be typed with the user's types.

   The descriptor with no VIEW node, `legacy_adesc k`, has type
   `asn1_impl_t k`; the relation `asn1_rel k` is defined as the relation of
   `legacy_adesc k`. *)

(* A KEEP-BYTES node (`D_KEEP`): the value `kval` together with, optionally,
   the bytes `kraw` of its DER encoding. Parsers always set `kraw` (to the
   input bytes of the value); writers ignore it. *)
noeq
type kept (t: Type0) = {
  kval: t;
  kraw: option (S.slice U8.t);
}

let view_law (#t #ty: Type0) (view: ty -> t) (mk: t -> ty) : prop =
  forall (x: t) . view (mk x) == x

noeq
type adesc : (#s: Set.set asn1_id_t) -> asn1_k s -> Type0 -> Type u#1 =
| D_ILC : id: asn1_id_t -> #k: asn1_content_k -> #t: Type0 -> cdesc k t -> adesc (ASN1_ILC id k) t
| D_CHOICE : lc: list (asn1_id_t & asn1_content_k) -> pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)) -> #t: Type0 -> lcdesc lc t -> adesc (ASN1_CHOICE_ILC lc pf) t
| D_ANY : adesc ASN1_ANY_ILC (S.slice U8.t)
| D_VIEW : #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> ty: Type0 -> view: (ty -> t) -> mk: (t -> ty) -> squash (view_law view mk) -> adesc k ty
| D_KEEP : #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> squash (Conf.wf k) -> adesc k (kept t)

and cdesc : asn1_content_k -> Type0 -> Type u#1 =
| CD_TERMINAL : k: asn1_terminal_k -> cdesc (ASN1_TERMINAL k) (asn1_terminal_impl_t k)
| CD_RESTRICTED : k: asn1_terminal_k -> r: asn1_restriction k -> cdesc (ASN1_RESTRICTED_TERMINAL k r) (asn1_terminal_impl_t k)
| CD_SEQUENCE : gitems: asn1_gen_items_lk -> #t: Type0 -> idesc (dsnd gitems) t -> cdesc (ASN1_SEQUENCE gitems) t
| CD_SET : ids: id_decs -> items: asn1_gen_items_l ids -> pf: squash (asn1_set_k_wf ids) -> #t: Type0 -> idesc items t -> cdesc (ASN1_SET ids items pf) t
| CD_SEQUENCE_OF : ne: bool -> #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> cdesc (ASN1_SEQUENCE_OF ne k) (ml t)
| CD_SET_OF : ne: bool -> #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> cdesc (ASN1_SET_OF ne k) (ml t)
| CD_PREFIXED : #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> cdesc (ASN1_PREFIXED k) t
| CD_ADB_NONE :
    ipd: id_decs -> prefix: asn1_gen_items_l ipd -> kid: asn1_id_t -> key_k: asn1_terminal_k ->
    ls: list (asn1_key_lit key_k & asn1_gen_items_lk) ->
    pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) ipd) -> pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)) ->
    #ts: Type0 -> sxdesc key_k ls ts -> #t: Type0 -> iadesc prefix ts t ->
    cdesc (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf') t
| CD_ADB_SOME :
    ipd: id_decs -> prefix: asn1_gen_items_l ipd -> kid: asn1_id_t -> key_k: asn1_terminal_k ->
    ls: list (asn1_key_lit key_k & asn1_gen_items_lk) -> fb: asn1_gen_items_lk ->
    pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) ipd) -> pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)) ->
    #tfb: Type0 -> idesc (dsnd fb) tfb ->
    #ts: Type0 -> fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts -> #t: Type0 -> iadesc prefix ts t ->
    cdesc (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf') t
| CD_VIEW : #k: asn1_content_k -> #t: Type0 -> cdesc k t -> ty: Type0 -> view: (ty -> t) -> mk: (t -> ty) -> squash (view_law view mk) -> cdesc k ty

and ddesc : (#s: Set.set asn1_id_t) -> (#d: asn1_decorator) -> asn1_decorated_k s d -> Type0 -> Type u#1 =
| DD_PLAIN : #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> ddesc (ASN1_PLAIN_ILC k) t
| DD_OPTION : #s: Set.set asn1_id_t -> #k: asn1_k s -> #t: Type0 -> adesc k t -> ddesc (ASN1_OPTION_ILC k) (option t)
| DD_DEFAULT : id: asn1_id_t -> #k: asn1_terminal_k -> defv: asn1_key_lit k -> ddesc (ASN1_DEFAULT_TERMINAL id #k defv) (option (asn1_terminal_impl_t k))
| DD_DEFAULT_RESTRICTED : id: asn1_id_t -> #k: asn1_terminal_k -> r: asn1_restriction k -> defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) = true } -> ddesc (ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv) (option (asn1_terminal_impl_t k))
| DD_VIEW : #s: Set.set asn1_id_t -> #d: asn1_decorator -> #dk: asn1_decorated_k s d -> #t: Type0 -> ddesc dk t -> ty: Type0 -> view: (ty -> t) -> mk: (t -> ty) -> squash (view_law view mk) -> ddesc dk ty

and idesc : (#ids: id_decs) -> asn1_gen_items_l ids -> Type0 -> Type u#1 =
| ID_NIL : idesc ASN1_GEN_ITEMS_NIL unit
| ID_SINGLE : #s: Set.set asn1_id_t -> #d: asn1_decorator -> #dk: asn1_decorated_k s d -> #t: Type0 -> ddesc dk t -> idesc (ASN1_GEN_ITEMS_CONS s d dk [] ASN1_GEN_ITEMS_NIL) t
| ID_CONS : #s: Set.set asn1_id_t -> #d: asn1_decorator -> #dk: asn1_decorated_k s d -> #t1: Type0 -> ddesc dk t1 ->
    #s2: Set.set asn1_id_t -> #d2: asn1_decorator -> #dk2: asn1_decorated_k s2 d2 -> #ids2: id_decs -> #tl2: asn1_gen_items_l ids2 -> #t2: Type0 ->
    idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) t2 ->
    idesc (ASN1_GEN_ITEMS_CONS s d dk ((s2, d2) :: ids2) (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (t1 & t2)

(* The items of an ANY DEFINED BY prefix, followed by a suffix of type `sfx` *)
and iadesc : (#ids: id_decs) -> asn1_gen_items_l ids -> Type0 -> Type0 -> Type u#1 =
| IA_NIL : #sfx: Type0 -> iadesc ASN1_GEN_ITEMS_NIL sfx sfx
| IA_SINGLE : #s: Set.set asn1_id_t -> #d: asn1_decorator -> #dk: asn1_decorated_k s d -> #t: Type0 -> ddesc dk t -> #sfx: Type0 -> iadesc (ASN1_GEN_ITEMS_CONS s d dk [] ASN1_GEN_ITEMS_NIL) sfx (t & sfx)
| IA_CONS : #s: Set.set asn1_id_t -> #d: asn1_decorator -> #dk: asn1_decorated_k s d -> #t1: Type0 -> ddesc dk t1 ->
    #s2: Set.set asn1_id_t -> #d2: asn1_decorator -> #dk2: asn1_decorated_k s2 d2 -> #ids2: id_decs -> #tl2: asn1_gen_items_l ids2 -> #sfx: Type0 -> #t2: Type0 ->
    iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfx t2 ->
    iadesc (ASN1_GEN_ITEMS_CONS s d dk ((s2, d2) :: ids2) (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) sfx (t1 & t2)

(* The supported keys of an ANY DEFINED BY, without fallback *)
and sxdesc : (key_k: asn1_terminal_k) -> list (asn1_key_lit key_k & asn1_gen_items_lk) -> Type0 -> Type u#1 =
| SX_NIL : key_k: asn1_terminal_k -> sxdesc key_k [] unit
| SX_SINGLE : key_k: asn1_terminal_k -> key: asn1_key_lit key_k -> it: asn1_gen_items_lk -> #t: Type0 -> idesc (dsnd it) t -> sxdesc key_k [(key, it)] t
| SX_CONS : key_k: asn1_terminal_k -> key: asn1_key_lit key_k -> it: asn1_gen_items_lk -> #t1: Type0 -> idesc (dsnd it) t1 ->
    #hd2: (asn1_key_lit key_k & asn1_gen_items_lk) -> #tl2: list (asn1_key_lit key_k & asn1_gen_items_lk) -> #t2: Type0 ->
    sxdesc key_k (hd2 :: tl2) t2 -> sxdesc key_k ((key, it) :: hd2 :: tl2) (either t1 t2)

(* The supported keys of an ANY DEFINED BY, with a fallback of type `fbt` *)
and fxdesc : (key_k: asn1_terminal_k) -> list (asn1_key_lit key_k & asn1_gen_items_lk) -> Type0 -> Type0 -> Type u#1 =
| FX_NIL : key_k: asn1_terminal_k -> #fbt: Type0 -> fxdesc key_k [] fbt fbt
| FX_SINGLE : key_k: asn1_terminal_k -> key: asn1_key_lit key_k -> it: asn1_gen_items_lk -> #t: Type0 -> idesc (dsnd it) t -> #fbt: Type0 -> fxdesc key_k [(key, it)] fbt (either t fbt)
| FX_CONS : key_k: asn1_terminal_k -> key: asn1_key_lit key_k -> it: asn1_gen_items_lk -> #t1: Type0 -> idesc (dsnd it) t1 ->
    #hd2: (asn1_key_lit key_k & asn1_gen_items_lk) -> #tl2: list (asn1_key_lit key_k & asn1_gen_items_lk) -> #fbt: Type0 -> #t2: Type0 ->
    fxdesc key_k (hd2 :: tl2) fbt t2 -> fxdesc key_k ((key, it) :: hd2 :: tl2) fbt (either t1 t2)

and lcdesc : list (asn1_id_t & asn1_content_k) -> Type0 -> Type u#1 =
| LC_NIL : lcdesc [] unit
| LC_SINGLE : id: asn1_id_t -> #c: asn1_content_k -> #t: Type0 -> cdesc c t -> lcdesc [(id, c)] t
| LC_CONS : id: asn1_id_t -> #c: asn1_content_k -> #t1: Type0 -> cdesc c t1 ->
    #hd2: (asn1_id_t & asn1_content_k) -> #tl2: list (asn1_id_t & asn1_content_k) -> #t2: Type0 ->
    lcdesc (hd2 :: tl2) t2 -> lcdesc ((id, c) :: hd2 :: tl2) (either t1 t2)

(* The relation of a descriptor. The spec type of a SEQUENCE OF / SET OF is
   a refinement of `list (asn1_t k)`, related by `mixed_list_match` to the
   mixed list, whose serialized chunks are related to
   `parse_nlist _ (asn1_as_parser k)`. A VIEW node relates a value through
   its view. *)

(* The bytes of a KEEP-BYTES node, if any: they hold the DER encoding of
   the spec value. *)
let keep_rel (#s: _) (k: asn1_k s) (pm: perm) (r: option (S.slice U8.t)) (y: asn1_t k) : slprop =
  match r with
  | None -> emp
  | Some sl -> pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) pm sl y

(* A mixed list returned by a parser: a serialized chunk of the input *)
let is_serialized (#t: Type0) (x: ml t) : prop =
  ItT.Base? x /\ ItT.Serialized? (ItT.Base?._0 x)

(* `arel kb d`: with `kb = true` (the relation ensured by parsers), every
   KEEP-BYTES node reachable without crossing a SEQUENCE OF / SET OF carries
   its bytes, and every SEQUENCE OF / SET OF is serialized (so its elements,
   once parsed, are related by `arel true`); with `kb = false` (the relation
   required by writers), KEEP-BYTES nodes may carry no bytes and lists may
   be built by the program. See `ASN1.Pulse.RelKeep` to go from one to the
   other. *)
let rec arel (kb: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (y: asn1_t k) : Tot slprop (decreases d) =
  match d with
  | D_ILC _ cd -> crel kb cd pm x y
  | D_CHOICE _ _ ld -> lcrel kb ld pm x y
  | D_ANY -> prel_slice_ser asn1_value_enc pm x y
  | D_VIEW d' _ view _ _ -> arel kb d' pm (view x) y
  | D_KEEP #_ #k' #t' d' _ ->
    let x' : kept t' = x in
    if kb
    then arel kb d' (pm /. 2.0R) x'.kval y ** keep_rel k' (pm /. 2.0R) x'.kraw y ** pure (Some? x'.kraw)
    else arel kb d' (pm /. 2.0R) x'.kval y ** keep_rel k' (pm /. 2.0R) x'.kraw y

and crel (kb: bool) (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (pm: perm) (x: t) (y: asn1_content_t k) : Tot slprop (decreases d) =
  match d with
  | CD_TERMINAL k' -> asn1_terminal_rel k' pm x y
  | CD_RESTRICTED k' _ -> asn1_terminal_rel k' pm x y
  | CD_SEQUENCE _ ld -> irel kb ld pm x y
  | CD_SET _ _ _ ld -> irel kb ld pm x y
  | CD_SEQUENCE_OF _ #_ #k' #t' d' ->
    if kb
    then It.mixed_list_match (arel kb d') ml_ops #asn1_strong_parser_kind (asn1_as_parser k') pm x y ** pure (is_serialized #t' x)
    else It.mixed_list_match (arel kb d') ml_ops #asn1_strong_parser_kind (asn1_as_parser k') pm x y
  | CD_SET_OF _ #_ #k' #t' d' ->
    if kb
    then It.mixed_list_match (arel kb d') ml_ops #asn1_strong_parser_kind (asn1_as_parser k') pm x y ** pure (is_serialized #t' x)
    else It.mixed_list_match (arel kb d') ml_ops #asn1_strong_parser_kind (asn1_as_parser k') pm x y
  | CD_PREFIXED d' -> arel kb d' pm x y
  | CD_ADB_NONE _ _ _ key_k ls _ _ dsx dpre ->
    iarel kb dpre
      #(make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls))
      (sxrel kb dsx)
      pm x y
  | CD_ADB_SOME _ _ _ key_k ls fb _ _ #tfb dfb dfx dpre ->
    iarel kb dpre
      #(make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core (dsnd fb)))
      (fxrel kb dfx (asn1_sequence_t_core (dsnd fb))
        (fun pm (z: asn1_terminal_impl_t key_k & tfb) key (v: asn1_sequence_t_core (dsnd fb)) ->
          asn1_terminal_rel key_k pm (fst z) key ** irel kb dfb pm (snd z) v))
      pm x y
  | CD_VIEW d' _ view _ _ -> crel kb d' pm (view x) y

and sxrel (kb: bool) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
  (pm: perm) (x: t) (y: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls))
: Tot slprop (decreases d)
= match d with
  | SX_NIL _ -> pure False
  | SX_SINGLE _ key' it di ->
    let (| key, v |) = y in
    if key = key_of_lit key_k key'
    then irel kb di pm x v
    else pure False
  | SX_CONS _ key' it #t1 di #_ #_ #t2 dtl ->
    let (| key, v |) = y in
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> if key = key_of_lit key_k key' then irel kb di pm a v else pure False
    | Inr b -> if key = key_of_lit key_k key' then pure False else sxrel kb dtl pm b (| key, v |)
    end

and fxrel (kb: bool) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (fbs: Type) (fbr: perm -> fbt -> asn1_terminal_t key_k -> fbs -> slprop)
  (pm: perm) (x: t) (y: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) fbs)
: Tot slprop (decreases d)
= match d with
  | FX_NIL _ ->
    let (| key, v |) = y in
    fbr pm x key v
  | FX_SINGLE _ key' it #t1 di ->
    let (| key, v |) = y in
    let x' : either t1 fbt = x in
    begin match x' with
    | Inl a -> if key = key_of_lit key_k key' then irel kb di pm a v else pure False
    | Inr b -> if key = key_of_lit key_k key' then pure False else fbr pm b key v
    end
  | FX_CONS _ key' it #t1 di #_ #_ #_ #t2 dtl ->
    let (| key, v |) = y in
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> if key = key_of_lit key_k key' then irel kb di pm a v else pure False
    | Inr b -> if key = key_of_lit key_k key' then pure False else fxrel kb dtl fbs fbr pm b (| key, v |)
    end

and lcrel (kb: bool) (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t) (pm: perm) (x: t) (y: make_gen_choice_type (asn1_lc_t lc)) : Tot slprop (decreases d) =
  match d with
  | LC_NIL -> pure False
  | LC_SINGLE id' cd ->
    let (| id, v |) = y in
    if id = id'
    then crel kb cd pm x v
    else pure False
  | LC_CONS id' #_ #t1 cd #_ #_ #t2 dtl ->
    let (| id, v |) = y in
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> if id = id' then crel kb cd pm a v else pure False
    | Inr b -> if id = id' then pure False else lcrel kb dtl pm b (| id, v |)
    end

and drel (kb: bool) (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (pm: perm) (x: t) (y: asn1_decorated_t_core dk) : Tot slprop (decreases d) =
  match d with
  | DD_PLAIN d' -> arel kb d' pm x y
  | DD_OPTION #_ #k' #t' d' ->
    let x' : option t' = x in
    let y' : option (asn1_t k') = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> arel kb d' pm a b
    | _ -> pure False
    end
  | DD_DEFAULT _ #k' defv ->
    let x' : option (asn1_terminal_impl_t k') = x in
    let y' : default_tv (key_of_lit k' defv) = y in
    begin match x', y' with
    | None, Default -> emp
    | Some a, Nondefault b -> asn1_terminal_rel k' pm a b
    | _ -> pure False
    end
  | DD_DEFAULT_RESTRICTED _ #k' r defv ->
    let x' : option (asn1_terminal_impl_t k') = x in
    let y' : default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k' defv) = y in
    begin match x', y' with
    | None, Default -> emp
    | Some a, Nondefault b -> asn1_terminal_rel k' pm a b
    | _ -> pure False
    end
  | DD_VIEW d' _ view _ _ -> drel kb d' pm (view x) y

and irel (kb: bool) (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (d: idesc ls t) (pm: perm) (x: t) (y: asn1_sequence_t_core ls) : Tot slprop (decreases d) =
  match d with
  | ID_NIL -> emp
  | ID_SINGLE dd -> drel kb dd pm x y
  | ID_CONS #_ #_ #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #t2 dtl ->
    let x' : t1 & t2 = x in
    let y' : asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) = y in
    drel kb dd pm (fst x') (fst y') ** irel kb dtl pm (snd x') (snd y')

and iarel (kb: bool) (#ids: _) (#ls: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (d: iadesc ls sfxi t) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm) (x: t) (y: asn1_sequence_any_t_core ls sfxs) : Tot slprop (decreases d) =
  match d with
  | IA_NIL -> sfxr pm x y
  | IA_SINGLE #_ #_ #dk #t1 dd ->
    let x' : t1 & sfxi = x in
    let y' : asn1_decorated_t_core dk & sfxs = y in
    drel kb dd pm (fst x') (fst y') ** sfxr pm (snd x') (snd y')
  | IA_CONS #_ #_ #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #_ #t2 dtl ->
    let x' : t1 & t2 = x in
    let y' : asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs = y in
    drel kb dd pm (fst x') (fst y') ** iarel kb dtl sfxr pm (snd x') (snd y')

(* The legacy descriptors: no VIEW node *)

let rec legacy_cdesc (k: asn1_content_k) : Tot (cdesc k (asn1_content_impl_t k)) (decreases k) =
  match k as k returns cdesc k (asn1_content_impl_t k) with
  | ASN1_RESTRICTED_TERMINAL k' r -> CD_RESTRICTED k' r
  | ASN1_TERMINAL k' -> CD_TERMINAL k'
  | ASN1_SEQUENCE gitems -> CD_SEQUENCE gitems (legacy_idesc (dsnd gitems))
  | ASN1_SET ids items pf -> CD_SET ids items pf (legacy_idesc items)
  | ASN1_SEQUENCE_OF ne k' -> CD_SEQUENCE_OF ne (legacy_adesc k')
  | ASN1_SET_OF ne k' -> CD_SET_OF ne (legacy_adesc k')
  | ASN1_PREFIXED k' -> CD_PREFIXED (legacy_adesc k')
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf' ->
    CD_ADB_NONE ipd prefix kid key_k ls pf pf' (legacy_sxdesc key_k ls) (legacy_iadesc prefix (asn1_adb_suffix_impl_t key_k ls None))
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf' ->
    CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' (legacy_idesc (dsnd fb))
      (legacy_fxdesc key_k ls (asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb)))
      (legacy_iadesc prefix (asn1_adb_suffix_impl_t key_k ls (Some (asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb)))))

and legacy_sxdesc (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Tot (sxdesc key_k ls (asn1_adb_suffix_impl_t key_k ls None)) (decreases ls) =
  match ls as ls returns sxdesc key_k ls (asn1_adb_suffix_impl_t key_k ls None) with
  | [] -> SX_NIL key_k
  | [(key, it)] -> SX_SINGLE key_k key it (legacy_idesc (dsnd it))
  | (key, it) :: hd2 :: tl2 -> SX_CONS key_k key it (legacy_idesc (dsnd it)) (legacy_sxdesc key_k (hd2 :: tl2))

and legacy_fxdesc (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fbt: Type0) : Tot (fxdesc key_k ls fbt (asn1_adb_suffix_impl_t key_k ls (Some fbt))) (decreases ls) =
  match ls as ls returns fxdesc key_k ls fbt (asn1_adb_suffix_impl_t key_k ls (Some fbt)) with
  | [] -> FX_NIL key_k #fbt
  | [(key, it)] -> FX_SINGLE key_k key it (legacy_idesc (dsnd it)) #fbt
  | (key, it) :: hd2 :: tl2 -> FX_CONS key_k key it (legacy_idesc (dsnd it)) (legacy_fxdesc key_k (hd2 :: tl2) fbt)

and legacy_lcdesc (lc: list (asn1_id_t & asn1_content_k)) : Tot (lcdesc lc (asn1_lc_impl_t lc)) (decreases lc) =
  match lc as lc returns lcdesc lc (asn1_lc_impl_t lc) with
  | [] -> LC_NIL
  | [(id, c)] -> LC_SINGLE id (legacy_cdesc c)
  | (id, c) :: hd2 :: tl2 -> LC_CONS id (legacy_cdesc c) (legacy_lcdesc (hd2 :: tl2))

and legacy_adesc (#s: _) (k: asn1_k s) : Tot (adesc k (asn1_impl_t k)) (decreases k) =
  match k as k returns adesc k (asn1_impl_t k) with
  | ASN1_ILC id k' -> D_ILC id (legacy_cdesc k')
  | ASN1_CHOICE_ILC lc pf -> D_CHOICE lc pf (legacy_lcdesc lc)
  | ASN1_ANY_ILC -> D_ANY

and legacy_ddesc (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot (ddesc dk (asn1_decorated_impl_t dk)) (decreases dk) =
  match dk as dk returns ddesc dk (asn1_decorated_impl_t dk) with
  | ASN1_PLAIN_ILC k -> DD_PLAIN (legacy_adesc k)
  | ASN1_OPTION_ILC k -> DD_OPTION (legacy_adesc k)
  | ASN1_DEFAULT_TERMINAL id #k defv -> DD_DEFAULT id #k defv
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv -> DD_DEFAULT_RESTRICTED id #k r defv

and legacy_idesc (#ids: _) (items: asn1_gen_items_l ids) : Tot (idesc items (asn1_items_impl_t items)) (decreases items) =
  match items as items returns idesc items (asn1_items_impl_t items) with
  | ASN1_GEN_ITEMS_NIL -> ID_NIL
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ID_SINGLE (legacy_ddesc dk)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) -> ID_CONS (legacy_ddesc dk) (legacy_idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))

and legacy_iadesc (#ids: _) (items: asn1_gen_items_l ids) (sfx: Type0) : Tot (iadesc items sfx (asn1_items_any_impl_t items sfx)) (decreases items) =
  match items as items returns iadesc items sfx (asn1_items_any_impl_t items sfx) with
  | ASN1_GEN_ITEMS_NIL -> IA_NIL
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> IA_SINGLE (legacy_ddesc dk)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) -> IA_CONS (legacy_ddesc dk) (legacy_iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfx)

(* The relation of today's representations: that of the legacy descriptors *)

let asn1_content_rel (k: asn1_content_k) : prel (asn1_content_impl_t k) (asn1_content_t k) = crel false (legacy_cdesc k)

let asn1_adb_rel (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: prel (asn1_adb_suffix_impl_t key_k ls None) (make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls))
= sxrel false (legacy_sxdesc key_k ls)

let asn1_adb_fb_rel (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbt: Type0) (fbs: Type) (fbr: perm -> fbt -> asn1_terminal_t key_k -> fbs -> slprop)
: prel (asn1_adb_suffix_impl_t key_k ls (Some fbt)) (make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) fbs)
= fxrel false (legacy_fxdesc key_k ls fbt) fbs fbr

let asn1_lc_rel (lc: list (asn1_id_t & asn1_content_k)) : prel (asn1_lc_impl_t lc) (make_gen_choice_type (asn1_lc_t lc)) = lcrel false (legacy_lcdesc lc)

let asn1_rel (#s: _) (k: asn1_k s) : prel (asn1_impl_t k) (asn1_t k) = arel false (legacy_adesc k)

let asn1_decorated_rel (#s: _) (#d: _) (dk: asn1_decorated_k s d) : prel (asn1_decorated_impl_t dk) (asn1_decorated_t_core dk) = drel false (legacy_ddesc dk)

let asn1_items_rel (#ids: _) (items: asn1_gen_items_l ids) : prel (asn1_items_impl_t items) (asn1_sequence_t_core items) = irel false (legacy_idesc items)

let asn1_items_any_rel (#ids: _) (items: asn1_gen_items_l ids) (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop)
: prel (asn1_items_any_impl_t items sfxi) (asn1_sequence_any_t_core items sfxs)
= iarel false (legacy_iadesc items sfxi) sfxr

(* The relations ensured by the legacy parsers *)

let asn1_prel (#s: _) (k: asn1_k s) : prel (asn1_impl_t k) (asn1_t k) = arel true (legacy_adesc k)

let asn1_content_prel (k: asn1_content_k) : prel (asn1_content_impl_t k) (asn1_content_t k) = crel true (legacy_cdesc k)

(* Equations, so that proofs need not unfold the relation of a whole schema *)

let asn1_rel_ilc_eq (id: asn1_id_t) (k: asn1_content_k) (pm: perm) (x: asn1_impl_t (ASN1_ILC id k)) (y: asn1_t (ASN1_ILC id k))
: Lemma (asn1_rel (ASN1_ILC id k) pm x y == asn1_content_rel k pm x y)
= ()

let asn1_rel_any_eq (pm: perm) (x: asn1_impl_t ASN1_ANY_ILC) (y: asn1_t ASN1_ANY_ILC)
: Lemma (asn1_rel ASN1_ANY_ILC pm x y == prel_slice_ser asn1_value_enc pm x y)
= ()

let asn1_content_rel_terminal_eq (k: asn1_terminal_k) (pm: perm) (x: asn1_content_impl_t (ASN1_TERMINAL k)) (y: asn1_content_t (ASN1_TERMINAL k))
: Lemma (asn1_content_rel (ASN1_TERMINAL k) pm x y == asn1_terminal_rel k pm x y)
= ()

let asn1_content_rel_seq_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y)
= assert (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y)
    by (FStar.Tactics.V2.norm [delta_only [`%asn1_content_rel]; iota; zeta]; FStar.Tactics.V2.trefl ())

let asn1_content_rel_set_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (y: asn1_content_t (ASN1_SET_OF ne k))
: Lemma (asn1_content_rel (ASN1_SET_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y)
= assert (asn1_content_rel (ASN1_SET_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y)
    by (FStar.Tactics.V2.norm [delta_only [`%asn1_content_rel]; iota; zeta]; FStar.Tactics.V2.trefl ())

let asn1_terminal_rel_leaf_eq (k: leaf_k) (pm: perm) (x: asn1_terminal_impl_t k) (y: asn1_terminal_t k)
: Lemma
  (requires (~ (ASN1_BOOLEAN? k \/ ASN1_NULL? k \/ ASN1_INTEGER? k \/ ASN1_BITSTRING? k)))
  (ensures (
    asn1_terminal_impl_t k == S.slice U8.t /\
    asn1_terminal_rel k pm x y == prel_slice_ser (leaf_enc k) pm x y))
= ()
