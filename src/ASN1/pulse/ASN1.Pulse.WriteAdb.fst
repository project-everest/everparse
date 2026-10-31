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
module WLm = ASN1.Pulse.Writer.Lemmas
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

inline_for_extraction
let cw_key_leaf (kid: asn1_id_t) (key_k: asn1_terminal_k { In.adb_key_supported key_k /\ ~ (ASN1_OID? key_k) /\ ~ (ASN1_PREFIXED_TERMINAL? key_k) })
  (u: squash (Conf.wf_terminal kid key_k)) (x: asn1_key_lit key_k)
: cwriter (key_enc kid key_k x)
= In.key_enc_list_correct key_k x;
  WL.leaf_value_enc_eq kid key_k (key_of_lit key_k x);
  cw_ext (cw_tlv kid (fun x' #xx out pos #v #p -> cw_bytes (In.key_enc_list key_k x) x' #xx out pos #v #p)) (key_enc kid key_k x) ()

inline_for_extraction
let cw_key_oid (kid: asn1_id_t) (key_k: asn1_terminal_k { ASN1_OID? key_k })
  (u: squash (Conf.wf_terminal kid key_k)) (x: asn1_key_lit key_k)
: cwriter (key_enc kid key_k x)
= [@inline_let] let x' : asn1_oid_t = x in
  oid_arcs_enc x';
  WL.leaf_value_enc_eq kid ASN1_OID x';
  cw_ext (cw_tlv kid (fun x0 #xx out pos #v #p -> cw_arcs (In.oid_enc x') x0 #xx out pos #v #p)) (key_enc kid key_k x) ()

let key_enc_prefixed (kid: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_key_lit (ASN1_PREFIXED_TERMINAL id2 k2))
: Lemma
  (requires (Conf.wf_terminal kid (ASN1_PREFIXED_TERMINAL id2 k2)))
  (ensures (key_enc kid (ASN1_PREFIXED_TERMINAL id2 k2) x == enc_tlv kid true (key_enc id2 k2 (In.prefixed_lit id2 k2 x))))
= In.key_of_lit_prefixed id2 k2 x;
  WL.terminal_prefixed_types (ASN1_PREFIXED_TERMINAL id2 k2) id2 k2;
  WL.terminal_prefixed_enc kid (ASN1_PREFIXED_TERMINAL id2 k2) id2 k2 (key_of_lit (ASN1_PREFIXED_TERMINAL id2 k2) x)

[@@In.asn1_pulse_attr]
let rec cw_key (kid: asn1_id_t) ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  ([@@@FStar.Attributes.monomorphize] x: asn1_key_lit key_k)
  (x': unit) (#xx: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (WL.wres (prel_emp unit unit 1.0R) (const_enc (key_enc kid key_k x)) x' xx out pos v p)
  (decreases key_k)
= [@inline_let] let vf : cwriter (key_enc kid key_k x) =
  (match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    key_enc_prefixed kid id2 k2 x;
    cw_ext (cw_tlv kid (fun x' #xx out pos #v #p -> cw_key id2 k2 () (In.prefixed_lit id2 k2 x) x' #xx out pos #v #p)) (key_enc kid key_k x) ()
  | ASN1_OID -> cw_key_oid kid key_k () x
  | _ -> cw_key_leaf kid key_k () x)
  in vf x' #xx out pos #v #p

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

(* Dispatching on the key, without a fallback *)

let adb_inl (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (a: asn1_items_impl_t (Mkdtuple2?._2 y))
: Tot (asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None)
= Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a

let adb_inr (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None)
: Tot (asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None)
= Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b

ghost
fn adb_single_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k [(kx, y)] None) (v: AL.ady key_k [(kx, y)])
requires asn1_adb_rel key_k [(kx, y)] pm x v
returns b: Ghost.erased (asn1_sequence_t_core (dsnd y))
ensures asn1_items_rel (dsnd y) pm x b ** Trade.trade (asn1_items_rel (dsnd y) pm x b) (asn1_adb_rel key_k [(kx, y)] pm x v) **
  pure (WLm.senc kid key_k [(kx, y)] v == pre_enc (key_enc kid key_k kx) (WLm.ienc (dsnd y)) b)
{
  RS.adb_single_eq kx y pm x v;
  if (dfst v = key_of_lit key_k kx) {
    WLm.senc_head kid kx y [] v;
    let b : Ghost.erased (asn1_sequence_t_core (dsnd y)) = Ghost.hide (AL.ady_head_val kx y [] v ());
    Trade.rewrite_with_trade (asn1_adb_rel key_k [(kx, y)] pm x v) (asn1_items_rel (dsnd y) pm x b);
    b
  } else {
    rewrite (asn1_adb_rel key_k [(kx, y)] pm x v) as (pure False);
    unreachable ()
  }
}

ghost
fn adb_cons_inl_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
requires asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v ** pure (x == adb_inl kx y hd2 tl2 a)
returns b: Ghost.erased (asn1_sequence_t_core (dsnd y))
ensures asn1_items_rel (dsnd y) pm a b ** Trade.trade (asn1_items_rel (dsnd y) pm a b) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) **
  pure (WLm.senc kid key_k ((kx, y) :: hd2 :: tl2) v == pre_enc (key_enc kid key_k kx) (WLm.ienc (dsnd y)) b)
{
  RS.adb_cons_inl_eq kx y hd2 tl2 pm a v;
  if (dfst v = key_of_lit key_k kx) {
    WLm.senc_head kid kx y (hd2 :: tl2) v;
    let b : Ghost.erased (asn1_sequence_t_core (dsnd y)) = Ghost.hide (AL.ady_head_val kx y (hd2 :: tl2) v ());
    Trade.rewrite_with_trade (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) (asn1_items_rel (dsnd y) pm a b);
    b
  } else {
    rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) as (pure False);
    unreachable ()
  }
}

ghost
fn adb_cons_inr_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) (bi: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
requires asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v ** pure (x == adb_inr kx y hd2 tl2 bi)
returns b: Ghost.erased (AL.ady key_k (hd2 :: tl2))
ensures asn1_adb_rel key_k (hd2 :: tl2) pm bi b ** Trade.trade (asn1_adb_rel key_k (hd2 :: tl2) pm bi b) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) **
  pure (WLm.senc kid key_k ((kx, y) :: hd2 :: tl2) v == WLm.senc kid key_k (hd2 :: tl2) b)
{
  RS.adb_cons_inr_eq kx y hd2 tl2 pm bi v;
  if (dfst v = key_of_lit key_k kx) {
    rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) as (pure False);
    unreachable ()
  } else {
    WLm.senc_tail kid kx y (hd2 :: tl2) v;
    let b : Ghost.erased (AL.ady key_k (hd2 :: tl2)) = Ghost.hide (AL.ady_tail_val kx y (hd2 :: tl2) v ());
    Trade.rewrite_with_trade (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm x v) (asn1_adb_rel key_k (hd2 :: tl2) pm bi b);
    b
  }
}

inline_for_extraction
fn write_adb_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) (pm: perm)
: W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k [] None) #(AL.ady key_k []) (asn1_adb_rel key_k [] pm) (WLm.senc kid key_k [])
= (x': asn1_adb_suffix_impl_t key_k [] None) (#x: Ghost.erased (AL.ady key_k [])) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (asn1_adb_rel key_k [] pm x' x) as (pure False);
  unreachable ()
}

inline_for_extraction
fn write_adb_single (kid: asn1_id_t) (#key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (wi: W.r2l_writer_f (asn1_items_rel (dsnd y) pm) (WLm.ienc (dsnd y)))
: W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k [(kx, y)] None) #(AL.ady key_k [(kx, y)]) (asn1_adb_rel key_k [(kx, y)] pm) (WLm.senc kid key_k [(kx, y)])
= (x': asn1_adb_suffix_impl_t key_k [(kx, y)] None) (#x: Ghost.erased (AL.ady key_k [(kx, y)])) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let b = adb_single_elim kid kx y pm x' x;
  let res = write_then_const wi (fun x0 #xx out pos #v #p -> cw_key kid key_k () kx x0 #xx out pos #v #p) x' #b out pos;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn write_adb_cons (kid: asn1_id_t) (#key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pm: perm)
  (wi: W.r2l_writer_f (asn1_items_rel (dsnd y) pm) (WLm.ienc (dsnd y)))
  (wt: W.r2l_writer_f (asn1_adb_rel key_k (hd2 :: tl2) pm) (WLm.senc kid key_k (hd2 :: tl2)))
: W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) #(AL.ady key_k ((kx, y) :: hd2 :: tl2)) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm) (WLm.senc kid key_k ((kx, y) :: hd2 :: tl2))
= (x': asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) (#x: Ghost.erased (AL.ady key_k ((kx, y) :: hd2 :: tl2))) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let x2 : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) = x';
  match x2 {
    Inl a -> {
      assert (pure (x' == adb_inl kx y hd2 tl2 a));
      let b = adb_cons_inl_elim kid kx y hd2 tl2 pm x' a x;
      let res = write_then_const wi (fun x0 #xx out pos #v #p -> cw_key kid key_k () kx x0 #xx out pos #v #p) a #b out pos;
      Trade.elim _ _;
      res
    }
    Inr bi -> {
      assert (pure (x' == adb_inr kx y hd2 tl2 bi));
      let b = adb_cons_inr_elim kid kx y hd2 tl2 pm x' bi x;
      let res = wt bi #b out pos;
      Trade.elim _ _;
      res
    }
  }
}

(* Dispatching on the key, with a fallback: the fallback payload, then the
   key (which is not a literal there) *)

inline_for_extraction
let write_terminal_f (kid: asn1_id_t) (key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k)) (pm: perm)
: W.r2l_writer_f #(asn1_terminal_impl_t key_k) #(asn1_terminal_t key_k) (asn1_terminal_rel key_k pm) (WL.terminal_enc kid key_k)
= fun x' #x out pos #v #p -> WL.r2l_write_terminal kid key_k () pm x' #x out pos #v #p

inline_for_extraction
fn write_fbr (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (u: squash (Conf.wf_terminal kid key_k)) (pm: perm)
  (wi: W.r2l_writer_f (asn1_items_rel (dsnd fb) pm) (WLm.ienc (dsnd fb)))
  (z: PA.fbt key_k fb) (#key: Ghost.erased (asn1_terminal_t key_k)) (#nv: Ghost.erased (PA.fbs fb))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
requires pts_to out v ** pts_to pos p ** PA.fbr key_k fb pm z key nv ** pure (SZ.v p <= Seq.length v)
returns res: bool
ensures exists* v' p' . pts_to out v' ** pts_to pos p' ** PA.fbr key_k fb pm z key nv **
  pure (W.r2l_post (Seq.append (WL.terminal_enc kid key_k key) (WLm.ienc (dsnd fb) nv)) (SZ.v p) v res (SZ.v p') v')
{
  RS.fbr_eq key_k fb pm z key nv;
  rewrite (PA.fbr key_k fb pm z key nv) as (asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) nv);
  let ok = wi (snd z) #nv out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** R.pts_to pos p1);
    let res = write_terminal_f kid key_k () pm (fst z) #key out pos;
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    W.r2l_post_append (WL.terminal_enc kid key_k key) (WLm.ienc (dsnd fb) nv) (SZ.v p) v (SZ.v p1) v1 res (SZ.v p2) v2;
    rewrite (asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) nv) as (PA.fbr key_k fb pm z key nv);
    res
  } else {
    rewrite (asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) nv) as (PA.fbr key_k fb pm z key nv);
    false
  }
}

inline_for_extraction
fn write_afb_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (u: squash (Conf.wf_terminal kid key_k)) (pm: perm)
  (wi: W.r2l_writer_f (asn1_items_rel (dsnd fb) pm) (WLm.ienc (dsnd fb)))
: W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k [] fb) (PA.afb_rel key_k [] fb pm) (WLm.fsenc kid key_k [] fb)
= (x': asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) (#x: Ghost.erased (AL.ady_fb key_k [] fb)) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  RS.afb_nil_eq fb pm x' x;
  rewrite (PA.afb_rel key_k [] fb pm x' x) as (PA.fbr key_k fb pm x' (dfst x) (AL.ady_fb_nil_val fb x));
  let res = write_fbr kid key_k fb u pm wi x' out pos;
  rewrite (PA.fbr key_k fb pm x' (dfst x) (AL.ady_fb_nil_val fb x)) as (PA.afb_rel key_k [] fb pm x' x);
  WLm.fsenc_nil kid key_k fb x;
  res
}

let afb_single_inl (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y))
: Tot (asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb)))
= Inl #_ #(PA.fbt key_k fb) a

let afb_single_inr (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (b: PA.fbt key_k fb)
: Tot (asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb)))
= Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b

let afb_inl (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y))
: Tot (asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb)))
= Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) a

let afb_inr (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb)))
: Tot (asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb)))
= Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b

ghost
fn afb_single_inl_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k [(kx, y)] fb)
requires PA.afb_rel key_k [(kx, y)] fb pm x v ** pure (x == afb_single_inl kx y fb a)
returns b: Ghost.erased (asn1_sequence_t_core (dsnd y))
ensures asn1_items_rel (dsnd y) pm a b ** Trade.trade (asn1_items_rel (dsnd y) pm a b) (PA.afb_rel key_k [(kx, y)] fb pm x v) **
  pure (WLm.fsenc kid key_k [(kx, y)] fb v == pre_enc (key_enc kid key_k kx) (WLm.ienc (dsnd y)) b)
{
  RS.afb_single_inl_eq kx y fb pm a v;
  if (dfst v = key_of_lit key_k kx) {
    WLm.fsenc_head kid kx y [] fb v;
    let b : Ghost.erased (asn1_sequence_t_core (dsnd y)) = Ghost.hide (AL.ady_fb_head_val kx y [] fb v ());
    Trade.rewrite_with_trade (PA.afb_rel key_k [(kx, y)] fb pm x v) (asn1_items_rel (dsnd y) pm a b);
    b
  } else {
    rewrite (PA.afb_rel key_k [(kx, y)] fb pm x v) as (pure False);
    unreachable ()
  }
}

ghost
fn afb_single_inr_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) (bi: PA.fbt key_k fb) (v: AL.ady_fb key_k [(kx, y)] fb)
requires PA.afb_rel key_k [(kx, y)] fb pm x v ** pure (x == afb_single_inr kx y fb bi)
returns b: Ghost.erased (AL.ady_fb key_k [] fb)
ensures PA.afb_rel key_k [] fb pm bi b ** Trade.trade (PA.afb_rel key_k [] fb pm bi b) (PA.afb_rel key_k [(kx, y)] fb pm x v) **
  pure (WLm.fsenc kid key_k [(kx, y)] fb v == WLm.fsenc kid key_k [] fb b)
{
  RS.afb_single_inr_eq kx y fb pm bi v;
  if (dfst v = key_of_lit key_k kx) {
    rewrite (PA.afb_rel key_k [(kx, y)] fb pm x v) as (pure False);
    unreachable ()
  } else {
    WLm.fsenc_tail kid kx y [] fb v;
    let b : Ghost.erased (AL.ady_fb key_k [] fb) = Ghost.hide (AL.ady_fb_tail_val kx y [] fb v ());
    RS.afb_nil_eq fb pm bi b;
    Trade.rewrite_with_trade (PA.afb_rel key_k [(kx, y)] fb pm x v) (PA.afb_rel key_k [] fb pm bi b);
    b
  }
}

ghost
fn afb_cons_inl_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
requires PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v ** pure (x == afb_inl kx y hd2 tl2 fb a)
returns b: Ghost.erased (asn1_sequence_t_core (dsnd y))
ensures asn1_items_rel (dsnd y) pm a b ** Trade.trade (asn1_items_rel (dsnd y) pm a b) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) **
  pure (WLm.fsenc kid key_k ((kx, y) :: hd2 :: tl2) fb v == pre_enc (key_enc kid key_k kx) (WLm.ienc (dsnd y)) b)
{
  RS.afb_cons_inl_eq kx y hd2 tl2 fb pm a v;
  if (dfst v = key_of_lit key_k kx) {
    WLm.fsenc_head kid kx y (hd2 :: tl2) fb v;
    let b : Ghost.erased (asn1_sequence_t_core (dsnd y)) = Ghost.hide (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ());
    Trade.rewrite_with_trade (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) (asn1_items_rel (dsnd y) pm a b);
    b
  } else {
    rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) as (pure False);
    unreachable ()
  }
}

ghost
fn afb_cons_inr_elim (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) (bi: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
requires PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v ** pure (x == afb_inr kx y hd2 tl2 fb bi)
returns b: Ghost.erased (AL.ady_fb key_k (hd2 :: tl2) fb)
ensures PA.afb_rel key_k (hd2 :: tl2) fb pm bi b ** Trade.trade (PA.afb_rel key_k (hd2 :: tl2) fb pm bi b) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) **
  pure (WLm.fsenc kid key_k ((kx, y) :: hd2 :: tl2) fb v == WLm.fsenc kid key_k (hd2 :: tl2) fb b)
{
  RS.afb_cons_inr_eq kx y hd2 tl2 fb pm bi v;
  if (dfst v = key_of_lit key_k kx) {
    rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) as (pure False);
    unreachable ()
  } else {
    WLm.fsenc_tail kid kx y (hd2 :: tl2) fb v;
    let b : Ghost.erased (AL.ady_fb key_k (hd2 :: tl2) fb) = Ghost.hide (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ());
    Trade.rewrite_with_trade (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm x v) (PA.afb_rel key_k (hd2 :: tl2) fb pm bi b);
    b
  }
}

inline_for_extraction
fn write_afb_single (kid: asn1_id_t) (#key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (wi: W.r2l_writer_f (asn1_items_rel (dsnd y) pm) (WLm.ienc (dsnd y)))
  (wt: W.r2l_writer_f (PA.afb_rel key_k [] fb pm) (WLm.fsenc kid key_k [] fb))
: W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k [(kx, y)] fb) (PA.afb_rel key_k [(kx, y)] fb pm) (WLm.fsenc kid key_k [(kx, y)] fb)
= (x': asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) (#x: Ghost.erased (AL.ady_fb key_k [(kx, y)] fb)) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let x2 : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (PA.fbt key_k fb) = x';
  match x2 {
    Inl a -> {
      assert (pure (x' == afb_single_inl kx y fb a));
      let b = afb_single_inl_elim kid kx y fb pm x' a x;
      let res = write_then_const wi (fun x0 #xx out pos #v #p -> cw_key kid key_k () kx x0 #xx out pos #v #p) a #b out pos;
      Trade.elim _ _;
      res
    }
    Inr bi -> {
      assert (pure (x' == afb_single_inr kx y fb bi));
      let b = afb_single_inr_elim kid kx y fb pm x' bi x;
      let res = wt bi #b out pos;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction
fn write_afb_cons (kid: asn1_id_t) (#key_k: asn1_terminal_k) (u: squash (Conf.wf_terminal kid key_k /\ In.adb_key_supported key_k))
  (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (wi: W.r2l_writer_f (asn1_items_rel (dsnd y) pm) (WLm.ienc (dsnd y)))
  (wt: W.r2l_writer_f (PA.afb_rel key_k (hd2 :: tl2) fb pm) (WLm.fsenc kid key_k (hd2 :: tl2) fb))
: W.r2l_writer_f #(asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm) (WLm.fsenc kid key_k ((kx, y) :: hd2 :: tl2) fb)
= (x': asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) (#x: Ghost.erased (AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let x2 : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) = x';
  match x2 {
    Inl a -> {
      assert (pure (x' == afb_inl kx y hd2 tl2 fb a));
      let b = afb_cons_inl_elim kid kx y hd2 tl2 fb pm x' a x;
      let res = write_then_const wi (fun x0 #xx out pos #v #p -> cw_key kid key_k () kx x0 #xx out pos #v #p) a #b out pos;
      Trade.elim _ _;
      res
    }
    Inr bi -> {
      assert (pure (x' == afb_inr kx y hd2 tl2 fb bi));
      let b = afb_cons_inr_elim kid kx y hd2 tl2 fb pm x' bi x;
      let res = wt bi #b out pos;
      Trade.elim _ _;
      res
    }
  }
}
