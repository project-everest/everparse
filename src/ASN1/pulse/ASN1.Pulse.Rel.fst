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

and asn1_adb_suffix_impl_t (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fbt: option Type0) : Tot Type0 (decreases ls) =
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

(* The relation. The spec type of a SEQUENCE OF / SET OF is a refinement of
   `list (asn1_t k')`, related by `mixed_list_match` to the mixed list,
   whose serialized chunks are related to `parse_nlist _ (asn1_as_parser k')`. *)

let rec asn1_content_rel (k: asn1_content_k) (pm: perm) (x: asn1_content_impl_t k) (y: asn1_content_t k) : Tot slprop (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> asn1_terminal_rel k' pm x y
  | ASN1_TERMINAL k' -> asn1_terminal_rel k' pm x y
  | ASN1_SEQUENCE gitems -> asn1_items_rel (dsnd gitems) pm x y
  | ASN1_SET _ items _ -> asn1_items_rel items pm x y
  | ASN1_SEQUENCE_OF _ k' -> It.mixed_list_match (asn1_rel k') ml_ops #asn1_strong_parser_kind (asn1_as_parser k') pm x y
  | ASN1_SET_OF _ k' -> It.mixed_list_match (asn1_rel k') ml_ops #asn1_strong_parser_kind (asn1_as_parser k') pm x y
  | ASN1_PREFIXED k' -> asn1_rel k' pm x y
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      asn1_items_any_rel prefix
        #(asn1_adb_suffix_impl_t key_k ls None)
        #(make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) ls))
        (asn1_adb_rel key_k ls)
        pm x y
    | Some fb ->
      let fbt = asn1_terminal_impl_t key_k & asn1_items_impl_t (dsnd fb) in
      asn1_items_any_rel prefix
        #(asn1_adb_suffix_impl_t key_k ls (Some fbt))
        #(make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) ls) (asn1_sequence_t_core (dsnd fb)))
        (asn1_adb_fb_rel key_k ls fbt (asn1_sequence_t_core (dsnd fb))
          (fun pm (z: asn1_terminal_impl_t key_k & asn1_items_impl_t (dsnd fb)) key (v: asn1_sequence_t_core (dsnd fb)) ->
            asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) v))
        pm x y
    end

and asn1_adb_rel (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk))
  (pm: perm) (x: asn1_adb_suffix_impl_t key_k ls None) (y: make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) ls))
: Tot slprop (decreases ls)
= match ls with
  | [] -> pure False
  | [(key', it)] ->
    let (| key, v |) = y in
    if key = key'
    then asn1_items_rel (dsnd it) pm x v
    else pure False
  | (key', it) :: tl ->
    let (| key, v |) = y in
    let x' : either (asn1_items_impl_t (dsnd it)) (asn1_adb_suffix_impl_t key_k tl None) = x in
    begin match x' with
    | Inl a -> if key = key' then asn1_items_rel (dsnd it) pm a v else pure False
    | Inr b -> if key = key' then pure False else asn1_adb_rel key_k tl pm b (| key, v |)
    end

and asn1_adb_fb_rel (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk))
  (fbt: Type0) (fbs: Type) (fbr: perm -> fbt -> asn1_terminal_t key_k -> fbs -> slprop)
  (pm: perm) (x: asn1_adb_suffix_impl_t key_k ls (Some fbt)) (y: make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) ls) fbs)
: Tot slprop (decreases ls)
= match ls with
  | [] ->
    let (| key, v |) = y in
    fbr pm x key v
  | [(key', it)] ->
    let (| key, v |) = y in
    let x' : either (asn1_items_impl_t (dsnd it)) fbt = x in
    begin match x' with
    | Inl a -> if key = key' then asn1_items_rel (dsnd it) pm a v else pure False
    | Inr b -> if key = key' then pure False else fbr pm b key v
    end
  | (key', it) :: tl ->
    let (| key, v |) = y in
    let x' : either (asn1_items_impl_t (dsnd it)) (asn1_adb_suffix_impl_t key_k tl (Some fbt)) = x in
    begin match x' with
    | Inl a -> if key = key' then asn1_items_rel (dsnd it) pm a v else pure False
    | Inr b -> if key = key' then pure False else asn1_adb_fb_rel key_k tl fbt fbs fbr pm b (| key, v |)
    end

and asn1_lc_rel (lc: list (asn1_id_t & asn1_content_k)) (pm: perm) (x: asn1_lc_impl_t lc) (y: make_gen_choice_type (asn1_lc_t lc)) : Tot slprop (decreases lc) =
  match lc with
  | [] -> pure False
  | [(id', c)] ->
    let (| id, v |) = y in
    if id = id'
    then asn1_content_rel c pm x v
    else pure False
  | (id', c) :: tl ->
    let (| id, v |) = y in
    let x' : either (asn1_content_impl_t c) (asn1_lc_impl_t tl) = x in
    begin match x' with
    | Inl a -> if id = id' then asn1_content_rel c pm a v else pure False
    | Inr b -> if id = id' then pure False else asn1_lc_rel tl pm b (| id, v |)
    end

and asn1_rel (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_impl_t k) (y: asn1_t k) : Tot slprop (decreases k) =
  match k with
  | ASN1_ILC _ k' -> asn1_content_rel k' pm x y
  | ASN1_CHOICE_ILC lc _ -> asn1_lc_rel lc pm x y
  | ASN1_ANY_ILC -> prel_slice_ser asn1_value_enc pm x y

and asn1_decorated_rel (#s: _) (#d: _) (dk: asn1_decorated_k s d) (pm: perm) (x: asn1_decorated_impl_t dk) (y: asn1_decorated_t_core dk) : Tot slprop (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> asn1_rel k pm x y
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_impl_t k) = x in
    let y' : option (asn1_t k) = y in
    begin match x', y' with
    | None, None -> emp
    | Some a, Some b -> asn1_rel k pm a b
    | _ -> pure False
    end
  | ASN1_DEFAULT_TERMINAL _ #k defv ->
    let x' : option (asn1_terminal_impl_t k) = x in
    let y' : default_tv defv = y in
    begin match x', y' with
    | None, Default -> emp
    | Some a, Nondefault b -> asn1_terminal_rel k pm a b
    | _ -> pure False
    end
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r defv ->
    let x' : option (asn1_terminal_impl_t k) = x in
    let y' : default_tv #(parse_filter_refine (restriction_pred r)) defv = y in
    begin match x', y' with
    | None, Default -> emp
    | Some a, Nondefault b -> asn1_terminal_rel k pm a b
    | _ -> pure False
    end

and asn1_items_rel (#ids: _) (items: asn1_gen_items_l ids) (pm: perm) (x: asn1_items_impl_t items) (y: asn1_sequence_t_core items) : Tot slprop (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> emp
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> asn1_decorated_rel dk pm x y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_impl_t dk & asn1_items_impl_t tl = x in
    let y' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = y in
    asn1_decorated_rel dk pm (fst x') (fst y') ** asn1_items_rel tl pm (snd x') (snd y')

and asn1_items_any_rel (#ids: _) (items: asn1_gen_items_l ids) (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm) (x: asn1_items_any_impl_t items sfxi) (y: asn1_sequence_any_t_core items sfxs) : Tot slprop (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfxr pm x y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_impl_t dk & sfxi = x in
    let y' : asn1_decorated_t_core dk & sfxs = y in
    asn1_decorated_rel dk pm (fst x') (fst y') ** sfxr pm (snd x') (snd y')
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_impl_t dk & asn1_items_any_impl_t tl sfxi = x in
    let y' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfxs = y in
    asn1_decorated_rel dk pm (fst x') (fst y') ** asn1_items_any_rel tl sfxr pm (snd x') (snd y')

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
