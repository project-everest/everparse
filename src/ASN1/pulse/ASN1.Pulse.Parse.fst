module ASN1.Pulse.Parse
#lang-pulse

(* Zero-copy parsers from validated ASN.1 DER bytes to the Pulse
   representations of `ASN1.Pulse.Rel`.

   A parser takes a slice holding EXACTLY the bytes of one value (as
   checked by a validator), and returns its Pulse representation, borrowing
   the input slice with the same permission: the relation `r pm res v`
   holds, and gives the slice back by a trade. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open ASN1.Base
open ASN1.Spec.ILC
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module SDER = LowParse.Spec.DER
module SVG = LowParse.Spec.VLGen
module ILC = ASN1.Pulse.ILC
module I = ASN1.Pulse.Identifier

(* The parser type *)

let parsed (#k: SB.parser_kind) (#t: Type) (p: SB.parser k t) (w: SB.bytes) (v: t) : prop =
  match SB.parse p w with
  | Some (v', n) -> v' == v /\ n == Seq.length w
  | None -> False

inline_for_extraction
let aparser (#t: Type0) (#u: Type0) (r: prel t u) (#k: SB.parser_kind) (p: SB.parser k u) : Type =
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#w: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased u) ->
  stt t
    (S.pts_to input #pm w ** pure (parsed p w v))
    (fun res -> r pm res v ** Trade.trade (r pm res v) (S.pts_to input #pm w))

inline_for_extraction
fn parse_ext
  (#t: Type0) (#u: Type0) (#r: prel t u)
  (#k1: Ghost.erased SB.parser_kind) (#p1: SB.parser k1 u)
  (f: aparser r p1)
  (#k2: Ghost.erased SB.parser_kind) (p2: SB.parser k2 u { forall b . SB.parse p1 b == SB.parse p2 b })
: aparser #t #u r #k2 p2
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  f input #pm #w #v
}

inline_for_extraction
fn parse_rel_ext
  (#t: Type0) (#u: Type0) (#r1: prel t u)
  (#k: Ghost.erased SB.parser_kind) (#p: SB.parser k u)
  (f: aparser r1 p)
  (r2: prel t u { forall pm x y . r1 pm x y == r2 pm x y })
: aparser #t #u r2 #k p
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let res = f input #pm #w #v;
  rewrite each (r1 pm res v) as (r2 pm res v);
  res
}

let slice_full (w: SB.bytes) : Lemma (Seq.slice w 0 (Seq.length w) == w) [SMTPat (Seq.slice w 0 (Seq.length w))]
= Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length w)) w

(* Leaves *)

(* Byte-carrying leaves: the content slice itself *)
inline_for_extraction
fn parse_slice_leaf (k: Ghost.erased leaf_k)
: aparser #(S.slice U8.t) #(asn1_terminal_t k) (prel_slice_ser (leaf_enc k)) #asn1_weak_parser_kind (asn1_terminal_as_parser k)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  leaf_enc_consumed k w;
  fold (prel_slice_ser (leaf_enc k) pm input v);
  intro_trade (prel_slice_ser (leaf_enc k) pm input v) (S.pts_to input #pm w) emp fn _ {
    unfold (prel_slice_ser (leaf_enc k) pm input v);
  };
  input
}

inline_for_extraction
fn parse_boolean ()
: aparser #bool #bool (prel_eq bool) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BOOLEAN)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  leaf_enc_consumed ASN1_BOOLEAN w;
  let b = S.(input.(0sz));
  let res = (b = 0xFFuy);
  fold (prel_eq bool pm res v);
  intro_trade (prel_eq bool pm res v) (S.pts_to input #pm w) (S.pts_to input #pm w) fn _ {
    unfold (prel_eq bool pm res v);
  };
  res
}

inline_for_extraction
fn parse_null ()
: aparser #unit #unit (prel_emp unit unit) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_NULL)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  fold (prel_emp unit unit pm () v);
  intro_trade (prel_emp unit unit pm () v) (S.pts_to input #pm w) (S.pts_to input #pm w) fn _ {
    unfold (prel_emp unit unit pm () v);
  };
  ()
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn parse_bitstring ()
: aparser #asn1_bitstring_impl #asn1_bitstring_t asn1_bitstring_rel #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BITSTRING)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  leaf_enc_consumed ASN1_BITSTRING w;
  S.pts_to_len input;
  let u = S.(input.(0sz));
  let sub = subslice_trade input 1sz (S.len input);
  Seq.lemma_eq_elim (Seq.slice w 1 (Seq.length w)) (BYTES_WITH_UNUSEDBITS?.b v);
  let res = { unused = u; bytes = sub };
  rewrite each sub as res.bytes;
  fold (asn1_bitstring_rel pm res v);
  intro_trade (asn1_bitstring_rel pm res v) (S.pts_to input #pm w)
    (Trade.trade (S.pts_to res.bytes #pm (Seq.slice w 1 (Seq.length w))) (S.pts_to input #pm w)) fn _ {
    unfold (asn1_bitstring_rel pm res v);
    with w' . assert (S.pts_to res.bytes #pm w');
    rewrite (S.pts_to res.bytes #pm w') as (S.pts_to res.bytes #pm (Seq.slice w 1 (Seq.length w)));
    Trade.elim _ _;
  };
  res
}

#pop-options

(* ANY: the whole TLV slice *)
inline_for_extraction
fn parse_any ()
: aparser #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) #asn1_strong_parser_kind ASN1.Spec.Value.parse_asn1_value
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  parse_asn1_value_consumed' w;
  fold (prel_slice_ser asn1_value_enc pm input v);
  intro_trade (prel_slice_ser asn1_value_enc pm input v) (S.pts_to input #pm w) emp fn _ {
    unfold (prel_slice_ser asn1_value_enc pm input v);
  };
  input
}

(* TLV: the content slice of an ILC *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn ilc_content
  (id: Ghost.erased asn1_id_t)
  (#ack: Ghost.erased asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (input: S.slice U8.t)
  (#pm: perm)
  (#w: Ghost.erased SB.bytes)
  (#v: Ghost.erased (asn1_content_t ack))
  requires S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind #(asn1_content_t ack) (parse_asn1_ILC (Ghost.reveal id) #(Ghost.reveal ack) p) w v)
  returns c: S.slice U8.t
  ensures exists* wc . S.pts_to c #pm wc ** Trade.trade (S.pts_to c #pm wc) (S.pts_to input #pm w) ** pure (parsed #asn1_weak_parser_kind #(asn1_content_t ack) p wc v)
{
  ILC.ilc_eq id #ack p w;
  S.pts_to_len input;
  let off1 = I.jump_identifier input 0sz;
  let wl = Ghost.hide (Seq.slice w (SZ.v off1) (Seq.length w));
  ILC.lc_eq #asn1_weak_parser_kind #(asn1_content_t ack) p wl;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) #asn1_weak_parser_kind #(asn1_content_t ack) p wl;
  let mut poff = off1;
  let r = ILC.vread_length input poff;
  match r {
    Some len -> {
      let off2 = !poff;
      Seq.slice_slice w (SZ.v off1) (Seq.length w) (SZ.v off2 - SZ.v off1) (Seq.length w - SZ.v off1);
      let c = subslice_trade input off2 (S.len input);
      c
    }
    None -> {
      unreachable ()
    }
  }
}

#pop-options

inline_for_extraction
fn parse_ilc
  (id: Ghost.erased asn1_id_t)
  (#ack: Ghost.erased asn1_content_k)
  (#t: Type0)
  (#r: prel t (asn1_content_t ack))
  (#p: asn1_weak_parser (asn1_content_t ack))
  (f: aparser #t #(asn1_content_t ack) r #asn1_weak_parser_kind p)
: aparser #t #(asn1_content_t ack) r #asn1_strong_parser_kind (parse_asn1_ILC (Ghost.reveal id) #(Ghost.reveal ack) p)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let c = ilc_content id #ack p input #pm #w #v;
  with wc . assert (S.pts_to c #pm wc);
  let res = f c #pm #wc #v;
  Trade.trans _ _ (S.pts_to input #pm w);
  res
}
