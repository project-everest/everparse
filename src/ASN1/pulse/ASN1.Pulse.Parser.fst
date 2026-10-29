module ASN1.Pulse.Parser
#lang-pulse

(* The zero-copy parser interpreter: from a validated ASN.1 DER schema
   value `k`, a parser from `asn1_as_parser k` to `asn1_rel k`. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.ILC
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.Interpreter
open ASN1.Pulse.ParseChoice
open ASN1.Pulse.ParseSequence
open ASN1.Pulse.ParseSeqOf
open ASN1.Pulse.ParseSet

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module ILC = ASN1.Pulse.ILC

let ares (#t: Type0) (#u: Type0) (r: prel t u) (#k: SB.parser_kind) (p: SB.parser k u)
  (input: S.slice U8.t) (pm: perm) (w: Ghost.erased SB.bytes) (v: Ghost.erased u) : Type
= stt t
    (S.pts_to input #pm w ** pure (parsed p w v))
    (fun res -> r pm res v ** Trade.trade (r pm res v) (S.pts_to input #pm w))

(* The subset of schemas currently supported *)

[@@asn1_pulse_attr]
let rec psupported_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL _ -> true
  | ASN1_RESTRICTED_TERMINAL _ _ -> true
  | ASN1_PREFIXED k' -> psupported_k k'
  | ASN1_SEQUENCE gitems -> psupported_items (dsnd gitems)
  | ASN1_SEQUENCE_OF _ k' -> psupported_k k'
  | ASN1_SET_OF _ k' -> psupported_k k'
  | ASN1_SET _ items _ -> psupported_items items && items_canon items
  | _ -> false

and psupported_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> psupported_dec dk && psupported_items tl

and psupported_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> psupported_k k
  | ASN1_OPTION_ILC k -> psupported_k k
  | _ -> true

and psupported_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (_, c) :: tl -> psupported_content c && psupported_lc tl

and psupported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> psupported_content k'
  | ASN1_CHOICE_ILC lc _ -> psupported_lc lc
  | ASN1_ANY_ILC -> true
  | _ -> false

[@@asn1_pulse_attr]
inline_for_extraction
let parse_integer (bound: pos)
: aparser #(asn1_terminal_impl_t (ASN1_INTEGER bound)) #(asn1_terminal_t (ASN1_INTEGER bound)) (asn1_terminal_rel (ASN1_INTEGER bound)) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER bound))
= if small_integer bound
  then coerce_eq () (parse_small_integer bound)
  else coerce_eq () (parse_big_integer bound)

[@@asn1_pulse_attr]
let rec parse_terminal ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_terminal_t k))
: Tot (ares (asn1_terminal_rel k) (asn1_terminal_as_parser k) input pm w v)
  (decreases k)
= [@inline_let] let vf : aparser #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) #asn1_weak_parser_kind (asn1_terminal_as_parser k) =
  (match k with
  | ASN1_BOOLEAN -> parse_boolean ()
  | ASN1_NULL -> parse_null ()
  | ASN1_INTEGER bound -> parse_integer bound
  | ASN1_BITSTRING -> parse_bitstring ()
  | ASN1_PREFIXED_TERMINAL id k' ->
    parse_ext (parse_ilc id #(ASN1_TERMINAL k') #_ #_ #(asn1_terminal_as_parser k') (fun input #pm #w #v -> parse_terminal k' input #pm #w #v)) #asn1_weak_parser_kind (asn1_terminal_as_parser k)
  | ASN1_OCTETSTRING -> parse_slice_leaf k
  | ASN1_PRINTABLESTRING -> parse_slice_leaf k
  | ASN1_UTF8STRING -> parse_slice_leaf k
  | ASN1_IA5STRING -> parse_slice_leaf k
  | ASN1_VISIBLESTRING -> parse_slice_leaf k
  | ASN1_BMPSTRING -> parse_slice_leaf k
  | ASN1_UNIVERSALSTRING -> parse_slice_leaf k
  | ASN1_TELETEXSTRING -> parse_slice_leaf k
  | ASN1_NUMERICSTRING -> parse_slice_leaf k
  | ASN1_VIDEOTEXSTRING -> parse_slice_leaf k
  | ASN1_GRAPHICSTRING -> parse_slice_leaf k
  | ASN1_GENERALSTRING -> parse_slice_leaf k
  | ASN1_OBJECTDESCRIPTOR -> parse_slice_leaf k
  | ASN1_OID -> parse_slice_leaf k
  | ASN1_RELATIVE_OID -> parse_slice_leaf k
  | ASN1_OID_IRI -> parse_slice_leaf k
  | ASN1_RELATIVE_OID_IRI -> parse_slice_leaf k
  | ASN1_UTCTIME -> parse_slice_leaf k
  | ASN1_GENERALIZEDTIME -> parse_slice_leaf k
  | ASN1_DATE -> parse_slice_leaf k
  | ASN1_TIME_OF_DAY -> parse_slice_leaf k
  | ASN1_DATE_TIME -> parse_slice_leaf k)
  in vf input #pm #w #v

[@@asn1_pulse_attr]
inline_for_extraction
let parse_restricted (k: asn1_terminal_k) (r: asn1_restriction k)
: aparser #(asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))
= parse_rel_ext
    (parse_ext (parse_filter #_ #_ #_ #_ #(asn1_terminal_as_parser k) (fun input #pm #w #v -> parse_terminal k input #pm #w #v) (restriction_pred r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)))
    (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r))

(* Whether an identifier belongs to an item *)

[@@asn1_pulse_attr]
inline_for_extraction
let phas_id_k (#s: _) (k: asn1_k s) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match k with
  | ASN1_ILC id0 _ -> ILC.asn1_id_eq id id0
  | ASN1_CHOICE_ILC lc _ -> has_id_lc lc id
  | ASN1_ANY_ILC -> true

[@@asn1_pulse_attr]
inline_for_extraction
let phas_id_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match dk with
  | ASN1_PLAIN_ILC k -> phas_id_k k id
  | ASN1_OPTION_ILC k -> phas_id_k k id
  | ASN1_DEFAULT_TERMINAL id0 _ -> ILC.asn1_id_eq id id0
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 _ _ -> ILC.asn1_id_eq id id0

(* Absent items *)

[@@asn1_pulse_attr]
inline_for_extraction
let dec_absent (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: dabsent dk
= match dk with
  | ASN1_PLAIN_ILC k -> dec_plain_absent k
  | ASN1_OPTION_ILC k -> dec_option_absent k
  | ASN1_DEFAULT_TERMINAL id0 #k defv -> dec_default_absent id0 #k defv
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv -> dec_default_restricted_absent id0 #k r defv

let rec parse_content ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (u: squash (psupported_content k))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_content_t k))
: Tot (ares (asn1_content_rel k) (asn1_content_as_parser k) input pm w v)
  (decreases k)
= [@inline_let] let vf : aparser #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) #asn1_weak_parser_kind (asn1_content_as_parser k) =
  (match k with
  | ASN1_TERMINAL k' -> parse_terminal k'
  | ASN1_RESTRICTED_TERMINAL k' r -> parse_restricted k' r
  | ASN1_PREFIXED k' ->
    parse_ext #_ #_ #_ #_ #(asn1_as_parser k') (fun input #pm #w #v -> parse_k k' () input #pm #w #v) #asn1_weak_parser_kind (asn1_content_as_parser k)
  | ASN1_SEQUENCE gitems ->
    seq_parser gitems (fun input #pm #w #v -> parse_items (dsnd gitems) () input #pm #w #v)
  | ASN1_SEQUENCE_OF ne k' -> seq_of_parser ne k'
  | ASN1_SET_OF ne k' -> set_of_parser ne k'
  | ASN1_SET _ items pf ->
    set_parser items pf () (fun input #pm #w #v -> parse_items items () input #pm #w #v))
  in vf input #pm #w #v

and parse_items (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (psupported_items ls))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core ls))
: Tot (sres ls input pm w v)
  (decreases ls)
= [@inline_let] let vf : sparser ls =
  (match ls with
  | ASN1_GEN_ITEMS_NIL -> seq_nil ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    seq_single dk (fun input #pm #w #v -> parse_dec dk () input #pm #w #v) (dec_absent dk)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    seq_cons dk dk2 tl2 (phas_id_dec dk)
      (fun input #pm #w #v -> parse_dec dk () input #pm #w #v)
      (dec_absent dk)
      (fun input #pm #w #v -> parse_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () input #pm #w #v))
  in vf input #pm #w #v

and parse_dec (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) ([@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (u: squash (psupported_dec dk))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_decorated_t_core dk))
: Tot (dres dk input pm w v)
  (decreases dk)
= [@inline_let] let vf : dpresent dk =
  (match dk with
  | ASN1_PLAIN_ILC k -> dec_plain_present k (fun input #pm #w #v -> parse_k k () input #pm #w #v)
  | ASN1_OPTION_ILC k -> dec_option_present k (fun input #pm #w #v -> parse_k k () input #pm #w #v)
  | ASN1_DEFAULT_TERMINAL id0 #k defv -> dec_default_present id0 #k defv (fun input #pm #w #v -> parse_terminal k input #pm #w #v)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv -> dec_default_restricted_present id0 #k r defv (parse_restricted k r))
  in vf input #pm #w #v

and parse_k (#s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (u: squash (psupported_k k))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_t k))
: Tot (ares (asn1_rel k) (asn1_as_parser k) input pm w v)
  (decreases k)
= [@inline_let] let vf : aparser #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) #asn1_strong_parser_kind (asn1_as_parser k) =
  (match k with
  | ASN1_ILC id k' ->
    parse_ilc id #k' #_ #_ #(asn1_content_as_parser k') (fun input #pm #w #v -> parse_content k' () input #pm #w #v)
  | ASN1_CHOICE_ILC lc pf ->
    choice_parser lc pf (fun id input #pm #w #v -> parse_choice lc pf () id input #pm #w #v)
  | ASN1_ANY_ILC ->
    parse_ext (parse_any ()) #asn1_strong_parser_kind (asn1_as_parser k))
  in vf input #pm #w #v

and parse_choice ([@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (u: squash (psupported_lc lc))
  (id: asn1_id_t) (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (make_gen_choice_type (asn1_lc_t lc)))
: Tot (cres lc pf id input pm w v)
  (decreases lc)
= [@inline_let] let vf : cparser lc pf =
  (match lc with
  | [] -> choice_nil pf
  | [(id', c)] ->
    choice_single id' c pf (parse_ilc id' #c #_ #_ #(asn1_content_as_parser c) (fun input #pm #w #v -> parse_content c () input #pm #w #v))
  | (id', c) :: hd2 :: tl2 ->
    choice_cons id' c hd2 tl2 pf
      (parse_ilc id' #c #_ #_ #(asn1_content_as_parser c) (fun input #pm #w #v -> parse_content c () input #pm #w #v))
      (fun id input #pm #w #v -> parse_choice (hd2 :: tl2) () () id input #pm #w #v))
  in vf id input #pm #w #v
