module ASN1.Pulse.WriteAdb
#lang-pulse

(* Right-to-left writers for ANY DEFINED BY: constant writers for the TLV
   of a key literal, computed at extraction time from the literal (no
   scratch buffer), and the combinators writing a selected payload then
   its key. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Spec.ToValue
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module Conf = ASN1.Spec.Conformance
module CE = ASN1.Spec.Content.Enc
module WL = ASN1.Pulse.WriteLeaf
module In = ASN1.Pulse.Interpreter
module ADB = ASN1.Pulse.AnyDefinedBy
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module RS = ASN1.Pulse.RelShare
module AL = ASN1.Pulse.ParseAdb.Lemmas
module PA = ASN1.Pulse.ParseAdb

(* Constant writers *)

let const_enc (e: SB.bytes) (_: unit) : GTot SB.bytes = e

inline_for_extraction
let cwriter (e: SB.bytes) : Type = W.r2l_writer_f #unit #unit (prel_emp unit unit 1.0R) (const_enc e)

inline_for_extraction
fn cw_ext (#e1: Ghost.erased SB.bytes) (w: cwriter e1) (e2: Ghost.erased SB.bytes) (sq: squash (Ghost.reveal e1 == Ghost.reveal e2))
: cwriter e2
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  w x' #x out pos
}

inline_for_extraction
fn cw_empty (_: unit)
: cwriter Seq.empty
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  W.r2l_post_empty (SZ.v p) v;
  true
}

(* `w1` is written after (that is, to the left of) `w2` *)
inline_for_extraction
fn cw_append (#e1 #e2: Ghost.erased SB.bytes) (w1: cwriter e1) (w2: cwriter e2)
: cwriter (Seq.append e1 e2)
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let res = w2 x' #x out pos;
  if (res) {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let res' = w1 x' #x out pos;
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    W.r2l_post_append e1 e2 (SZ.v p) v (SZ.v p1) v1 res' (SZ.v p2) v2;
    res'
  } else {
    W.r2l_post_false_weaken e2 (Seq.append e1 e2) (SZ.v p) v (SZ.v p) v;
    false
  }
}

inline_for_extraction
fn cw_byte (h: U8.t)
: cwriter (Seq.create 1 h)
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  W.r2l_write_indexed 1sz (fun _ -> h) (Ghost.hide (Seq.create 1 h)) out pos
}

inline_for_extraction
fn cw_tlv (id: asn1_id_t) (#e: Ghost.erased SB.bytes) (w: cwriter e)
: cwriter (enc_tlv id true e)
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  WL.r2l_write_tlv id #unit #unit #(prel_emp unit unit 1.0R) #(const_enc e) w x' #x out pos
}

(* Byte lists *)

let seq_of_list_cons (h: U8.t) (t: list U8.t)
: Lemma (Seq.seq_of_list (h :: t) == Seq.append (Seq.create 1 h) (Seq.seq_of_list t))
= Seq.lemma_seq_of_list_induction (h :: t);
  Seq.lemma_eq_elim (Seq.seq_of_list (h :: t)) (Seq.append (Seq.create 1 h) (Seq.seq_of_list t))

let seq_of_list_nil (_: unit)
: Lemma (Seq.seq_of_list #U8.t [] == Seq.empty)
= Seq.lemma_seq_of_list_induction #U8.t [];
  Seq.lemma_eq_elim (Seq.seq_of_list #U8.t []) Seq.empty

[@@In.asn1_pulse_attr]
let rec cw_bytes ([@@@FStar.Attributes.monomorphize] l: list U8.t)
  (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (prel_emp unit unit 1.0R) (const_enc (Seq.seq_of_list l)) x' x out pos v p)
  (decreases l)
= [@inline_let] let vf : cwriter (Seq.seq_of_list l) =
  (match l with
  | [] ->
    seq_of_list_nil ();
    cw_ext (cw_empty ()) (Seq.seq_of_list l) ()
  | h :: t ->
    seq_of_list_cons h t;
    cw_ext (cw_append (cw_byte h) (fun x' #x out pos #v #p -> cw_bytes t x' #x out pos #v #p)) (Seq.seq_of_list l) ())
  in vf x' #x out pos #v #p

(* Subidentifiers (X.690 8.19.2) *)

let enc_arc_short (a: U32.t)
: Lemma (requires (U32.v a < 128))
  (ensures (CE.enc_arc a == Seq.create 1 (Cast.uint32_to_uint8 a)))
= ()

inline_for_extraction
let arc_len (a: U32.t { 128 <= U32.v a }) : Tot (n: SZ.t { SZ.v n == id_bound a + 1 }) =
  SZ.add (SZ.uint16_to_sizet (Cast.uint32_to_uint16 (WL.rt_bound a))) 1sz

inline_for_extraction
let arc_byte (a: U32.t { 128 <= U32.v a }) (i: SZ.t { SZ.v i < id_bound a + 1 })
: Tot (b: U8.t { U8.v b == WL.id_b a (SZ.v i) })
= assert_norm (pow2 32 == 4294967296);
  let m = SZ.sizet_to_uint32 i in
  assert (SZ.v i <= 4);
  FStar.Math.Lemmas.small_mod (SZ.v i) (pow2 32);
  assert (U32.v m == SZ.v i);
  WL.rt_id_b a m

let arc_index' (a: U32.t { 128 <= U32.v a }) (i: nat { i < id_bound a + 1 })
: Lemma (SZ.fits i /\ i < Seq.length (CE.enc_arc a) /\ Seq.index (CE.enc_arc a) i == arc_byte a (SZ.uint_to_t i))
= WL.enc_long_index a;
  SZ.fits_at_least_16 i;
  U8.v_inj (Seq.index (CE.enc_arc a) i) (arc_byte a (SZ.uint_to_t i))

let arc_index (a: U32.t { 128 <= U32.v a })
: Lemma (Seq.length (CE.enc_arc a) == id_bound a + 1 /\
    (forall (i: nat) . i < id_bound a + 1 ==> Seq.index (CE.enc_arc a) i == arc_byte a (SZ.uint_to_t i)))
= WL.enc_long_index a;
  Classical.forall_intro (arc_index' a)

inline_for_extraction
fn cw_arc (a: U32.t)
: cwriter (CE.enc_arc a)
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  if (U32.lt a 128ul) {
    enc_arc_short a;
    W.r2l_write_indexed 1sz (fun _ -> Cast.uint32_to_uint8 a) (Ghost.hide (CE.enc_arc a)) out pos
  } else {
    arc_index a;
    W.r2l_write_indexed (arc_len a) (arc_byte a) (Ghost.hide (CE.enc_arc a)) out pos
  }
}

[@@In.asn1_pulse_attr]
let rec cw_arcs ([@@@FStar.Attributes.monomorphize] l: list U32.t)
  (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (prel_emp unit unit 1.0R) (const_enc (CE.list_enc CE.enc_arc l)) x' x out pos v p)
  (decreases l)
= [@inline_let] let vf : cwriter (CE.list_enc CE.enc_arc l) =
  (match l with
  | [] -> cw_ext (cw_empty ()) (CE.list_enc CE.enc_arc l) ()
  | h :: t ->
    cw_ext (cw_append (cw_arc h) (fun x' #x out pos #v #p -> cw_arcs t x' #x out pos #v #p)) (CE.list_enc CE.enc_arc l) ())
  in vf x' #x out pos #v #p

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let oid_arcs_enc (x: asn1_oid_t)
: Lemma (CE.list_enc CE.enc_arc (ADB.oid_enc x) == CE.oid_enc x)
= match x with
  | a :: b :: tl ->
    assert (U32.v (List.Tot.hd (ADB.oid_enc x)) == 40 * U32.v a + U32.v b);
    assert (List.Tot.hd (ADB.oid_enc x) == CE.oid_head x)
#pop-options

(* Key literals: the TLV of the key, with identifier `kid` *)

let key_enc (kid: asn1_id_t) (key_k: asn1_terminal_k) (x: asn1_key_lit key_k) : GTot SB.bytes =
  WL.terminal_enc kid key_k (key_of_lit key_k x)

(* Raw key literals: the TLV of a key literal, with no requirement on the
   key schema (used by the raw writers, whose output is validated
   afterwards). This coincides with `key_enc` for well-formed, supported
   keys *)

let raw_key_list (k: asn1_terminal_k { ~ (ASN1_OID? k) /\ ~ (ASN1_RELATIVE_OID? k) /\ ~ (ASN1_PREFIXED_TERMINAL? k) }) (x: asn1_key_lit k) : Tot (list U8.t) =
  match k with
  | ASN1_BOOLEAN -> let x : bool = x in [if x then 0xFFuy else 0x00uy]
  | ASN1_NULL -> []
  | ASN1_INTEGER bound -> let x : asn1_int_lit bound = x in (x <: list U8.t)
  | ASN1_BITSTRING -> let x : asn1_bitstring_lit = x in fst x :: snd x
  | ASN1_PRINTABLESTRING -> let x : asn1_printablestring_t = x in In.char_list_bytes x
  | ASN1_IA5STRING -> let x : asn1_ia5string_t = x in In.char_list_bytes x
  | ASN1_VISIBLESTRING -> let x : asn1_visiblestring_t = x in In.char_list_bytes x
  | ASN1_NUMERICSTRING -> let x : asn1_numericstring_t = x in In.char_list_bytes x
  | _ -> let x : list U8.t = x in x

let rec raw_key_enc (kid: asn1_id_t) (key_k: asn1_terminal_k) (x: asn1_key_lit key_k) : Tot SB.bytes (decreases key_k) =
  match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> enc_tlv kid true (raw_key_enc id2 k2 (In.prefixed_lit id2 k2 x))
  | ASN1_OID -> let x' : asn1_oid_t = x in enc_tlv kid true (CE.list_enc CE.enc_arc (In.oid_enc x'))
  | ASN1_RELATIVE_OID -> let x' : asn1_relative_oid_t = x in enc_tlv kid true (CE.list_enc CE.enc_arc x')
  | _ -> enc_tlv kid true (Seq.seq_of_list (raw_key_list key_k x))

[@@In.asn1_pulse_attr]
let rec cw_raw_key (kid: asn1_id_t) ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  ([@@@FStar.Attributes.monomorphize] x: asn1_key_lit key_k)
  (x': unit) (#xx: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (prel_emp unit unit 1.0R) (const_enc (raw_key_enc kid key_k x)) x' xx out pos v p)
  (decreases key_k)
= [@inline_let] let vf : cwriter (raw_key_enc kid key_k x) =
  (match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    cw_ext (cw_tlv kid (fun x' #xx out pos #v #p -> cw_raw_key id2 k2 (In.prefixed_lit id2 k2 x) x' #xx out pos #v #p)) (raw_key_enc kid key_k x) ()
  | ASN1_OID ->
    [@inline_let] let x' : asn1_oid_t = x in
    cw_ext (cw_tlv kid (fun x0 #xx out pos #v #p -> cw_arcs (In.oid_enc x') x0 #xx out pos #v #p)) (raw_key_enc kid key_k x) ()
  | ASN1_RELATIVE_OID ->
    [@inline_let] let x' : asn1_relative_oid_t = x in
    cw_ext (cw_tlv kid (fun x0 #xx out pos #v #p -> cw_arcs x' x0 #xx out pos #v #p)) (raw_key_enc kid key_k x) ()
  | _ ->
    cw_ext (cw_tlv kid (fun x0 #xx out pos #v #p -> cw_bytes (raw_key_list key_k x) x0 #xx out pos #v #p)) (raw_key_enc kid key_k x) ())
  in vf x' #xx out pos #v #p

(* Writing a payload, then a constant (the TLV of the key literal selecting
   it) to its left *)

let pre_enc (#t: Type) (e: SB.bytes) (enc: t -> GTot SB.bytes) (x: t) : GTot SB.bytes =
  Seq.append e (enc x)

inline_for_extraction
fn write_then_const (#t' #t: Type0) (#vm: t' -> t -> slprop) (#enc: t -> GTot SB.bytes) (w: W.r2l_writer_f vm enc)
  (#e: Ghost.erased SB.bytes) (cw: cwriter e)
: W.r2l_writer_f #t' #t vm (pre_enc e enc)
= (x': t') (#x: Ghost.erased t) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let ok = w x' #x out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** R.pts_to pos p1);
    fold (prel_emp unit unit 1.0R () ());
    let res = cw () #() out pos;
    unfold (prel_emp unit unit 1.0R () ());
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    W.r2l_post_append e (enc x) (SZ.v p) v (SZ.v p1) v1 res (SZ.v p2) v2;
    res
  } else {
    false
  }
}
