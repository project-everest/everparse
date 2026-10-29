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

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base

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
  | _ -> false

and psupported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> psupported_content k'
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

let rec parse_content ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (u: squash (psupported_content k))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_content_t k))
: Tot (ares (asn1_content_rel k) (asn1_content_as_parser k) input pm w v)
  (decreases k)
= [@inline_let] let vf : aparser #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) #asn1_weak_parser_kind (asn1_content_as_parser k) =
  (match k with
  | ASN1_TERMINAL k' -> parse_terminal k'
  | ASN1_RESTRICTED_TERMINAL k' r ->
    parse_rel_ext
      (parse_ext (parse_filter #_ #_ #_ #_ #(asn1_terminal_as_parser k') (fun input #pm #w #v -> parse_terminal k' input #pm #w #v) (restriction_pred r)) #asn1_weak_parser_kind (asn1_content_as_parser k))
      (asn1_content_rel k)
  | ASN1_PREFIXED k' ->
    parse_ext #_ #_ #_ #_ #(asn1_as_parser k') (fun input #pm #w #v -> parse_k k' () input #pm #w #v) #asn1_weak_parser_kind (asn1_content_as_parser k))
  in vf input #pm #w #v

and parse_k (#s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (u: squash (psupported_k k))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_t k))
: Tot (ares (asn1_rel k) (asn1_as_parser k) input pm w v)
  (decreases k)
= [@inline_let] let vf : aparser #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) #asn1_strong_parser_kind (asn1_as_parser k) =
  (match k with
  | ASN1_ILC id k' ->
    parse_ilc id #k' #_ #_ #(asn1_content_as_parser k') (fun input #pm #w #v -> parse_content k' () input #pm #w #v)
  | ASN1_ANY_ILC ->
    parse_ext (parse_any ()) #asn1_strong_parser_kind (asn1_as_parser k))
  in vf input #pm #w #v
