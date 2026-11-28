module ASN1.Pulse.ParseSeqOf
#lang-pulse

(* Zero-copy parsing of SEQUENCE OF and SET OF: the contents are left
   serialized, as a `Serialized` mixed list over the content slice; the
   parser only counts the elements, walking their identifiers and length
   headers. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module SL = LowParse.Spec.List
module VC = LowParse.Spec.VCList
module T = LowParse.Tot.Combinators
module It = LowParse.PulseParse.Iterator
module ItT = LowParse.PulseParse.Iterator.Type
module LPB = LowParse.PulseParse.Base
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module L = ASN1.Pulse.ParseSequence.Lemmas
module PS = ASN1.Pulse.ParseSequence
module SO = ASN1.Pulse.SetOf
module ASet = ASN1.Spec.Set

(* Every element consumes exactly its identifier, length header and
   contents *)

#push-options "--fuel 1 --ifuel 1"
let tlv_consumed (#s: _) (k: asn1_k s) (b: SB.bytes)
: Lemma (match SB.parse (asn1_as_parser k) b with
    | Some (_, n) -> L.tlv_size b == Some n
    | None -> True)
= L.k_id_then k b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) -> L.k_twin_shaped' k id (Seq.slice b c1 (Seq.length b))
#pop-options

(* The contents are a plain list of elements *)

let seq_of_content (ne: bool) (#s: _) (k: asn1_k s) (w: SB.bytes) (v: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma
  (requires parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k)) w v)
  (ensures parsed (SL.parse_list #asn1_strong_parser_kind (asn1_as_parser k)) w v)
= assert (SB.parse (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k)) w == SB.parse (parse_sized_list ne (asn1_as_parser k)) w);
  T.parse_filter_eq (LowParse.Tot.List.parse_list (asn1_as_parser k)) (list_size_ok ne) w

let set_of_content (ne: bool) (#s: _) (k: asn1_k s) (w: SB.bytes) (v: asn1_content_t (ASN1_SET_OF ne k))
: Lemma
  (requires parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET_OF ne k)) w v)
  (ensures parsed (SL.parse_list #asn1_strong_parser_kind (asn1_as_parser k)) w v)
= let p = asn1_as_parser k in
  assert (SB.parse (asn1_content_as_parser (ASN1_SET_OF ne k)) w == SB.parse (parse_sized_set ne p) w);
  T.parse_filter_eq #asn1_weak_parser_kind (ASet.parse_asn1_set_of p) (list_size_ok ne) w;
  let q = ASet.tot_parse_byte_sorted_list ASet.lex_byte_order p in
  assert (SB.parse (ASet.parse_asn1_set_of p) w == SB.parse q w);
  assert (SB.parse q w == SB.parse (ASet.parse_byte_sorted_list (ASet.prop_order_of_bool_order ASet.lex_byte_order) #_ #asn1_strong_parser_kind p) w);
  SC.parse_synth_eq
    (SC.parse_filter (SL.parse_list #asn1_strong_parser_kind p) (ASet.parse_byte_sorted_list_filter (ASet.prop_order_of_bool_order ASet.lex_byte_order) #_ #asn1_strong_parser_kind p))
    (ASet.synth_byte_sorted_list (ASet.prop_order_of_bool_order ASet.lex_byte_order) #_ #asn1_strong_parser_kind p)
    w;
  SC.parse_filter_eq
    (SL.parse_list #asn1_strong_parser_kind p)
    (ASet.parse_byte_sorted_list_filter (ASet.prop_order_of_bool_order ASet.lex_byte_order) #_ #asn1_strong_parser_kind p)
    w

(* One step of the counting loop *)

let list_rest (#s: _) (k: asn1_k s) (w: SB.bytes) (off: nat) (n: nat) : prop =
  off <= Seq.length w /\
  (match SB.parse (SL.parse_list #asn1_strong_parser_kind (asn1_as_parser k)) (Seq.slice w off (Seq.length w)) with
   | Some (l, _) -> List.Tot.length l == n
   | None -> False)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let list_rest_step (#s: _) (k: asn1_k s) (w: SB.bytes) (off: nat) (n: nat)
: Lemma
  (requires list_rest k w off n /\ off < Seq.length w)
  (ensures (match L.tlv_size (Seq.slice w off (Seq.length w)) with
    | Some c -> c > 0 /\ n > 0 /\ off + c <= Seq.length w /\ list_rest k w (off + c) (n - 1)
    | None -> False))
= let p = asn1_as_parser k in
  let b = Seq.slice w off (Seq.length w) in
  SL.parse_list_eq #asn1_strong_parser_kind p b;
  tlv_consumed k b;
  let Some (l, _) = SB.parse (SL.parse_list #asn1_strong_parser_kind p) b in
  assert (List.Tot.length l == n);
  let Some (_, c) = SB.parse p b in
  assert (c > 0);
  let b' = Seq.slice b c (Seq.length b) in
  Seq.slice_slice w off (Seq.length w) c (Seq.length b);
  assert (b' == Seq.slice w (off + c) (Seq.length w));
  let Some (l', _) = SB.parse (SL.parse_list #asn1_strong_parser_kind p) b' in
  assert (List.Tot.length l == 1 + List.Tot.length l');
  assert (L.tlv_size b == Some c)
#pop-options

let tlv_size_at_arith (off off1 off2 c1 c2 l: nat)
: Lemma (requires off1 == off + c1 /\ off2 == off1 + c2) (ensures off + (c1 + c2 + l) == off2 + l)
= ()

let tlv_size_at (w: SB.bytes) (off: nat) (off1: nat) (off2: nat) (len: U32.t)
: Lemma
  (requires (
    off <= Seq.length w /\
    (match SB.parse parse_asn1_identifier_U32 (Seq.slice w off (Seq.length w)) with Some (_, c) -> off1 == off + c | None -> False) /\
    off1 <= Seq.length w /\
    (match SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w off1 (Seq.length w)) with Some (len', c2) -> (len' <: U32.t) == len /\ off2 == off1 + c2 | None -> False)))
  (ensures (let r = L.tlv_size (Seq.slice w off (Seq.length w)) in Some? r /\ off + Some?.v r == off2 + U32.v len))
= let b = Seq.slice w off (Seq.length w) in
  let c1 = snd (Some?.v (SB.parse parse_asn1_identifier_U32 b)) in
  assert (off1 == off + c1);
  assert (Seq.equal (Seq.slice b c1 (Seq.length b)) (Seq.slice w off1 (Seq.length w)));
  let c2 = snd (Some?.v (SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w off1 (Seq.length w)))) in
  PS.tlv_size_eq b c1 c2 len;
  tlv_size_at_arith off off1 off2 c1 c2 (U32.v len)

#push-options "--z3rlimit 32 --fuel 0 --ifuel 1"
let list_rest_next (#s: _) (k: asn1_k s) (w: SB.bytes) (off: nat) (off1: nat) (off2: nat) (len: U32.t) (n: nat)
: Lemma
  (requires (
    list_rest k w off n /\ off < Seq.length w /\
    (match SB.parse parse_asn1_identifier_U32 (Seq.slice w off (Seq.length w)) with Some (_, c) -> off1 == off + c | None -> False) /\
    off1 <= Seq.length w /\
    (match SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w off1 (Seq.length w)) with Some (len', c2) -> (len' <: U32.t) == len /\ off2 == off1 + c2 | None -> False)))
  (ensures (
    n > 0 /\ off < off2 + U32.v len /\ off2 + U32.v len <= Seq.length w /\
    list_rest k w (off2 + U32.v len) (n - 1)))
= list_rest_step k w off n;
  tlv_size_at w off off1 off2 len;
  let Some c = L.tlv_size (Seq.slice w off (Seq.length w)) in
  assert (off + c == off2 + U32.v len)
#pop-options

let tlv_parts (w: SB.bytes) (off: nat)
: Lemma
  (requires off <= Seq.length w /\ Some? (L.tlv_size (Seq.slice w off (Seq.length w))))
  (ensures (match SB.parse parse_asn1_identifier_U32 (Seq.slice w off (Seq.length w)) with
    | Some (_, c) -> off + c <= Seq.length w /\ Some? (SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w (off + c) (Seq.length w)))
    | None -> False))
= let b = Seq.slice w off (Seq.length w) in
  let Some (_, c) = SB.parse parse_asn1_identifier_U32 b in
  assert (Seq.equal (Seq.slice b c (Seq.length b)) (Seq.slice w (off + c) (Seq.length w)));
  ILC.length_eq (Seq.slice w (off + c) (Seq.length w))

let list_rest_end (#s: _) (k: asn1_k s) (w: SB.bytes) (off: nat) (n: nat)
: Lemma
  (requires list_rest k w off n /\ off >= Seq.length w)
  (ensures n == 0)
= Seq.slice_length w;
  SL.parse_list_eq #asn1_strong_parser_kind (asn1_as_parser k) (Seq.slice w off (Seq.length w))

inline_for_extraction
let sz_add_u32 (a: SZ.t) (b: U32.t)
: Pure SZ.t (requires SZ.fits (SZ.v a + U32.v b)) (ensures fun r -> SZ.v r == SZ.v a + U32.v b)
= SZ.add a (SZ.uint32_to_sizet b)

(* Counting the elements *)

inline_for_extraction
fn count_elements
  (#s: Ghost.erased (Set.set asn1_id_t)) (k: Ghost.erased (asn1_k s))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (list (asn1_t k)))
requires S.pts_to input #pm w ** pure (parsed (SL.parse_list #asn1_strong_parser_kind (asn1_as_parser k)) w v)
returns res: SZ.t
ensures S.pts_to input #pm w ** pure (SZ.v res == List.Tot.length v)
{
  S.pts_to_len input;
  let len = S.len input;
  Seq.slice_length w;
  assert (pure (list_rest k w 0 (List.Tot.length v)));
  let mut poff = 0sz;
  let mut pcnt = 0sz;
  while (
    let off = !poff;
    SZ.lt off len
  ) invariant exists* off cnt .
    R.pts_to poff off **
    R.pts_to pcnt cnt **
    S.pts_to input #pm w **
    pure (
      SZ.v off <= Seq.length w /\
      SZ.v cnt <= SZ.v off /\
      SZ.v cnt <= List.Tot.length v /\
      list_rest k w (SZ.v off) (List.Tot.length v - SZ.v cnt)
    )
    decreases (SZ.v len - SZ.v (!poff))
  {
    let off = !poff;
    let cnt = !pcnt;
    list_rest_step k w (SZ.v off) (List.Tot.length v - SZ.v cnt);
    tlv_parts w (SZ.v off);
    let oid = I.vread_identifier input poff;
    match oid {
      Some id -> {
        let off1 = !poff;
        assert (pure (match SB.parse parse_asn1_identifier_U32 (Seq.slice w (SZ.v off) (Seq.length w)) with Some (_, c) -> SZ.v off1 == SZ.v off + c | None -> False));
        let ol = ILC.vread_length input poff;
        match ol {
          Some l -> {
            let off2 = !poff;
            assert (pure (match SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w (SZ.v off1) (Seq.length w)) with Some (len', c2) -> (len' <: U32.t) == l /\ SZ.v off2 == SZ.v off1 + c2 | None -> False));
            list_rest_next k w (SZ.v off) (SZ.v off1) (SZ.v off2) l (List.Tot.length v - SZ.v cnt);
            SZ.fits_lte (SZ.v off2 + U32.v l) (Seq.length w);
            SZ.fits_lte (SZ.v cnt + 1) (Seq.length w);
            let noff = sz_add_u32 off2 l;
            let ncnt = SZ.add cnt 1sz;
            assert (pure (SZ.v noff == SZ.v off2 + U32.v l /\ SZ.v ncnt == SZ.v cnt + 1));
            assert (pure (List.Tot.length v - SZ.v ncnt == List.Tot.length v - SZ.v cnt - 1));
            poff := noff;
            pcnt := ncnt;
          }
          None -> {
            unreachable ()
          }
        }
      }
      None -> {
        unreachable ()
      }
    }
  };
  let off = !poff;
  let cnt = !pcnt;
  list_rest_end k w (SZ.v off) (List.Tot.length v - SZ.v cnt);
  cnt
}

(* The mixed list: the whole contents, serialized *)

let ml_match0 (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : prel (ml t) (list (asn1_t k)) =
  It.mixed_list_match (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k)

let ml_match (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (l: list (asn1_t k)) : slprop =
  ml_match0 d pm x l ** pure (is_serialized x)

let serialized_ml (t: Type0) (count: SZ.t) (input: S.slice U8.t) : ml t =
  ItT.Base (ItT.Serialized 0.5R count input)

let ml_match_n_eq (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (count: SZ.t) (input: S.slice U8.t) (pm: perm) (l: list (asn1_t k))
: Lemma (ml_match0 d pm (serialized_ml t count input) l ==
    It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized 0.5R count input)) l)
= assert (ml_match0 d pm (serialized_ml t count input) l ==
    It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized 0.5R count input)) l)
    by (FStar.Tactics.V2.norm [delta_only [`%ml_match0; `%serialized_ml; `%It.mixed_list_match; `%ItT.mixed_list_length; `%ItT.base_mixed_list_length; `%ml_ops; `%LowParse.PulseParse.Iterator.IntOps.sizet_ops; `%LowParse.PulseParse.Iterator.IntOps.__proj__Mkint_ops__item__v]; iota; zeta; primops]; FStar.Tactics.V2.trefl ())

let nlist_parsed (#s: _) (k: asn1_k s) (w: SB.bytes) (v: list (asn1_t k))
: Lemma
  (requires parsed (SL.parse_list #asn1_strong_parser_kind (asn1_as_parser k)) w v)
  (ensures LPB.pts_to_parsed_strong_prefix_prop (VC.parse_nlist (0 + List.Tot.length v) #asn1_strong_parser_kind (asn1_as_parser k)) w v)
= VC.parse_list_parse_nlist #asn1_strong_parser_kind (asn1_as_parser k) w

#push-options "--fuel 1 --ifuel 1"
let split_at_0 (#t: Type) (l: list t) : Lemma (l == snd (List.Tot.splitAt 0 l)) = ()
#pop-options

let as_nlist (#t: Type) (l: list t) : Tot (VC.nlist (0 + List.Tot.length l) t) = l

let half_eq (pm: perm) : Lemma (pm /. 2.0R == pm *. 0.5R /\ pm /. 2.0R +. pm /. 2.0R == pm) = ()

inline_for_extraction
fn list_parser
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (list (asn1_t k)))
requires S.pts_to input #pm w ** pure (parsed (SL.parse_list #asn1_strong_parser_kind (asn1_as_parser k)) w v)
returns res: ml t
ensures ml_match d pm res v ** Trade.trade (ml_match d pm res v) (S.pts_to input #pm w)
{
  let count = count_elements k input #pm #w #v;
  S.pts_to_len input;
  S.share input;
  half_eq pm;
  rewrite (S.pts_to input #(pm /. 2.0R) w) as (S.pts_to input #(pm *. 0.5R) w);
  nlist_parsed k w v;
  It.pts_to_parsed_strong_prefix_fold (VC.parse_nlist (0 + List.Tot.length v) #asn1_strong_parser_kind (asn1_as_parser k)) input #(pm *. 0.5R) #w (as_nlist (Ghost.reveal v));
  split_at_0 (Ghost.reveal v);
  fold (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Serialized 0.5R count input) v);
  let res : ml t = ItT.Base (ItT.Serialized 0.5R count input);
  fold (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized 0.5R count input)) v);
  ml_match_n_eq d count input pm v;
  rewrite (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized 0.5R count input)) v)
    as (ml_match0 d pm res v);
  fold (ml_match d pm res v);
  intro_trade (ml_match d pm res v) (S.pts_to input #pm w) (S.pts_to input #(pm /. 2.0R) w) fn _ {
    ml_match_n_eq d count input pm v;
    unfold (ml_match d pm res v);
    rewrite (ml_match0 d pm res v)
      as (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized 0.5R count input)) v);
    unfold (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized 0.5R count input)) v);
    unfold (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Serialized 0.5R count input) v);
    with l_all . unfold (LPB.pts_to_parsed_strong_prefix (VC.parse_nlist (0 + SZ.v count) #asn1_strong_parser_kind (asn1_as_parser k)) input #(pm *. 0.5R) l_all);
    with w' . assert (S.pts_to input #(pm *. 0.5R) w');
    half_eq pm;
    rewrite (S.pts_to input #(pm *. 0.5R) w') as (S.pts_to input #(pm /. 2.0R) w');
    S.gather input;
    rewrite (S.pts_to input #(pm /. 2.0R +. pm /. 2.0R) w) as (S.pts_to input #pm w);
  };
  res
}

let seq_of_list (ne: Ghost.erased bool) (#s: Ghost.erased (Set.set asn1_id_t)) (k: Ghost.erased (asn1_k s)) (v: Ghost.erased (asn1_content_t (ASN1_SEQUENCE_OF ne k)))
: Ghost.erased (list (asn1_t k))
= let l : list (asn1_t k) = Ghost.reveal v in Ghost.hide l

let set_of_list (ne: Ghost.erased bool) (#s: Ghost.erased (Set.set asn1_id_t)) (k: Ghost.erased (asn1_k s)) (v: Ghost.erased (asn1_content_t (ASN1_SET_OF ne k)))
: Ghost.erased (list (asn1_t k))
= let l : list (asn1_t k) = Ghost.reveal v in Ghost.hide l

let crel_seq_of_eq (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (crel true (CD_SEQUENCE_OF ne d) pm x y == ml_match d pm x y)
= assert (crel true (CD_SEQUENCE_OF ne d) pm x y == ml_match d pm x y)
    by (FStar.Tactics.V2.norm [delta_only [`%crel; `%ml_match; `%ml_match0]; iota; zeta]; FStar.Tactics.V2.trefl ())

let crel_set_of_eq (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (y: asn1_content_t (ASN1_SET_OF ne k))
: Lemma (crel true (CD_SET_OF ne d) pm x y == ml_match d pm x y)
= assert (crel true (CD_SET_OF ne d) pm x y == ml_match d pm x y)
    by (FStar.Tactics.V2.norm [delta_only [`%crel; `%ml_match; `%ml_match0]; iota; zeta]; FStar.Tactics.V2.trefl ())

(* The SEQUENCE OF and SET OF content parsers *)

inline_for_extraction
fn seq_of_parser (ne: Ghost.erased bool) (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
: aparser #(ml t) #(asn1_content_t (ASN1_SEQUENCE_OF ne k)) (crel true (CD_SEQUENCE_OF ne (Ghost.reveal d))) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seq_of_content ne k w v;
  let vl : Ghost.erased (list (asn1_t k)) = seq_of_list ne k v;
  let res : ml t = list_parser d input #pm #w #vl;
  crel_seq_of_eq ne d pm res v;
  PS.rel_rewrite #(ml_match d pm res vl) (crel true (CD_SEQUENCE_OF ne (Ghost.reveal d)) pm res v);
  res
}

inline_for_extraction
fn set_of_parser (ne: Ghost.erased bool) (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
: aparser #(ml t) #(asn1_content_t (ASN1_SET_OF ne k)) (crel true (CD_SET_OF ne (Ghost.reveal d))) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET_OF ne k))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  set_of_content ne k w v;
  let vl : Ghost.erased (list (asn1_t k)) = set_of_list ne k v;
  let res : ml t = list_parser d input #pm #w #vl;
  crel_set_of_eq ne d pm res v;
  PS.rel_rewrite #(ml_match d pm res vl) (crel true (CD_SET_OF ne (Ghost.reveal d)) pm res v);
  res
}
