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

#push-options "--fuel 0 --ifuel 1 --z3rlimit 16"
let ilc_content_spec
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (w: SB.bytes)
  (v: asn1_content_t ack)
: Lemma
  (requires (parsed #asn1_strong_parser_kind #(asn1_content_t ack) (parse_asn1_ILC id #ack p) w v))
  (ensures (
    match SB.parse ASN1.Spec.IdentifierU32.parse_asn1_identifier_U32 (Seq.slice w 0 (Seq.length w)) with
    | None -> False
    | Some (_, c1) ->
      c1 <= Seq.length w /\ (
      match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w c1 (Seq.length w)) with
      | None -> False
      | Some (_, c2) ->
        c1 + c2 <= Seq.length w /\
        parsed #asn1_weak_parser_kind #(asn1_content_t ack) p (Seq.slice w (c1 + c2) (Seq.length w)) v)))
= assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w);
  ILC.ilc_eq id #ack p w;
  let Some (_, c1) = SB.parse ASN1.Spec.IdentifierU32.parse_asn1_identifier_U32 w in
  let wl = Seq.slice w c1 (Seq.length w) in
  ILC.lc_eq #asn1_weak_parser_kind #(asn1_content_t ack) p wl;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) #asn1_weak_parser_kind #(asn1_content_t ack) p wl;
  let Some (_, c2) = SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) wl in
  Seq.slice_slice w c1 (Seq.length w) c2 (Seq.length w - c1)
#pop-options

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
  ilc_content_spec id #ack p w v;
  S.pts_to_len input;
  let off1 = I.jump_identifier input 0sz;
  let mut poff = off1;
  let r = ILC.vread_length input poff;
  match r {
    Some len -> {
      let off2 = !poff;
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

(* INTEGER *)

module E = LowParse.Endianness
module INT = ASN1.Spec.Content.INTEGER
module I64 = FStar.Int64

(* Two's complement big-endian value of a byte sequence *)
let signed_be (b: SB.bytes) : GTot int =
  if Seq.length b = 0 then 0
  else if U8.v (Seq.index b 0) >= 128
  then E.be_to_n b - pow2 (8 * Seq.length b)
  else E.be_to_n b

let signed_be_bounds (b: SB.bytes) : Lemma
  (requires (Seq.length b > 0))
  (ensures (
    - (pow2 (8 * Seq.length b - 1)) <= signed_be b /\
    signed_be b < pow2 (8 * Seq.length b - 1)
  ))
= E.lemma_be_to_n_is_bounded b;
  INT.be_to_n_msb b;
  FStar.Math.Lemmas.pow2_plus (8 * Seq.length b - 1) 1

let signed_be_one (b: SB.bytes) : Lemma
  (requires (Seq.length b == 1))
  (ensures (signed_be b == (if U8.v (Seq.index b 0) >= 128 then U8.v (Seq.index b 0) - 256 else U8.v (Seq.index b 0))))
= INT.be_to_n_singleton b;
  assert_norm (pow2 8 == 256)

let signed_be_snoc (b: SB.bytes) (x: U8.t) : Lemma
  (requires (Seq.length b > 0))
  (ensures (signed_be (Seq.snoc b x) == signed_be b * 256 + U8.v x))
= let b1 = Seq.create 1 x in
  Seq.lemma_eq_elim (Seq.snoc b x) (Seq.append b b1);
  E.be_to_n_append b b1;
  INT.be_to_n_singleton b1;
  assert_norm (pow2 8 == 256);
  FStar.Math.Lemmas.pow2_plus (8 * Seq.length b) 8

let mk_integer'_signed_be (b: SB.bytes) : Lemma
  (requires (INT.valid_unsigned_repr b))
  (ensures (INT.mk_integer' b == signed_be b))
= INT.be_to_n_msb b

let parse_integer_eq (bound: pos) (w: SB.bytes) (v: asn1_integer_t bound) : Lemma
  (requires (parsed #asn1_weak_parser_kind #(asn1_terminal_t (ASN1_INTEGER bound)) (asn1_terminal_as_parser (ASN1_INTEGER bound)) w v))
  (ensures (
    Seq.length w <= bound /\
    INT.valid_unsigned_repr w /\
    v == signed_be w
  ))
= assert (SB.parse (asn1_terminal_as_parser (ASN1_INTEGER bound)) w == INT.parse_untagged_bounded_integer' bound w);
  mk_integer'_signed_be w

#push-options "--z3rlimit 32"
let big_integer_not_fits (w: SB.bytes) : Lemma
  (requires (INT.valid_unsigned_repr w /\ Seq.length w > 8))
  (ensures (~ (fits_i64 (INT.mk_integer' w))))
= let n = Seq.length w in
  INT.mk_integer'_eq w;
  let x = INT.mk_integer' w in
  let s = Some?.v (INT.mk_integer_aux w) in
  assert (x == s);
  assert (INT.domain n x);
  FStar.Math.Lemmas.pow2_le_compat (8 * (n - 1) - 1) 63;
  FStar.Math.Lemmas.pow2_le_compat (8 * (n - 1)) 64;
  FStar.Math.Lemmas.pow2_plus (8 * (n - 1)) 8;
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 63 == 9223372036854775808);
  assert_norm (pow2 64 == 18446744073709551616)
#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
fn read_int64
  (input: S.slice U8.t)
  (#pm: perm)
  (#w: Ghost.erased SB.bytes)
  requires S.pts_to input #pm w ** pure (0 < Seq.length w /\ Seq.length w <= 8)
  returns res: I64.t
  ensures S.pts_to input #pm w ** pure (I64.v res == signed_be w)
{
  S.pts_to_len input;
  let len = S.len input;
  let b0 = S.(input.(0sz));
  Seq.lemma_eq_elim (Seq.slice w 0 1) (Seq.create 1 b0);
  signed_be_one (Seq.slice w 0 1);
  let i0 = FStar.Int.Cast.uint8_to_int64 b0;
  let init = (if U8.lt b0 128uy then i0 else I64.sub i0 256L);
  let mut pacc = init;
  let mut pi = 1sz;
  while (
    let i = !pi;
    SZ.lt i len
  ) invariant exists* acc i .
    S.pts_to input #pm w **
    pts_to pacc acc **
    pts_to pi i **
    pure (
      1 <= SZ.v i /\ SZ.v i <= Seq.length w /\
      I64.v acc == signed_be (Seq.slice w 0 (SZ.v i))
    )
    decreases (SZ.v len - SZ.v (!pi))
  {
    let i = !pi;
    let acc = !pacc;
    let b = S.(input.(i));
    let wi = Ghost.hide (Seq.slice w 0 (SZ.v i));
    Seq.lemma_eq_elim (Seq.slice w 0 (SZ.v i + 1)) (Seq.snoc wi b);
    signed_be_snoc wi b;
    signed_be_bounds wi;
    signed_be_bounds (Seq.slice w 0 (SZ.v i + 1));
    FStar.Math.Lemmas.pow2_le_compat 63 (8 * (SZ.v i + 1) - 1);
    FStar.Math.Lemmas.pow2_plus (8 * SZ.v i - 1) 8;
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 63 == 9223372036854775808);
    let acc' = I64.add (I64.mul acc 256L) (FStar.Int.Cast.uint8_to_int64 b);
    pacc := acc';
    pi := SZ.add i 1sz;
  };
  !pacc
}

#pop-options

inline_for_extraction
fn parse_small_integer (bound: pos { small_integer bound })
: aparser #I64.t #(asn1_integer_t bound) (asn1_small_int_rel bound) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER bound))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  parse_integer_eq bound w v;
  let res = read_int64 input;
  fold (asn1_small_int_rel bound pm res v);
  intro_trade (asn1_small_int_rel bound pm res v) (S.pts_to input #pm w) (S.pts_to input #pm w) fn _ {
    unfold (asn1_small_int_rel bound pm res v);
  };
  res
}

inline_for_extraction
fn parse_big_integer (bound: pos)
: aparser #asn1_int_impl #(asn1_integer_t bound) (asn1_int_rel bound) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER bound))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  parse_integer_eq bound w v;
  S.pts_to_len input;
  if (SZ.lte (S.len input) 8sz) {
    let i = read_int64 input;
    let res = Small i;
    rewrite (pure (I64.v i == Ghost.reveal v)) as (asn1_int_rel bound pm res v);
    intro_trade (asn1_int_rel bound pm res v) (S.pts_to input #pm w) (S.pts_to input #pm w) fn _ {
      rewrite (asn1_int_rel bound pm res v) as (pure (I64.v i == Ghost.reveal v));
    };
    res
  } else {
    big_integer_not_fits w;
    mk_integer'_signed_be w;
    leaf_enc_consumed (ASN1_INTEGER bound) w;
    let res = Big input;
    fold (prel_slice_ser (integer_enc bound) pm input v);
    rewrite (prel_slice_ser (integer_enc bound) pm input v ** pure (~ (fits_i64 v))) as (asn1_int_rel bound pm res v);
    intro_trade (asn1_int_rel bound pm res v) (S.pts_to input #pm w) emp fn _ {
      rewrite (asn1_int_rel bound pm res v) as (prel_slice_ser (integer_enc bound) pm input v ** pure (~ (fits_i64 v)));
      unfold (prel_slice_ser (integer_enc bound) pm input v);
    };
    res
  }
}

(* Restrictions: the representation of a refined value is that of the
   underlying value *)

let prel_refine (#t: Type0) (#u: Type) (r: prel t u) (f: u -> bool) : prel t (LowParse.Spec.Combinators.parse_filter_refine f) =
  fun pm x y -> r pm x y

inline_for_extraction
fn parse_filter
  (#t: Type0) (#u: Type0) (#r: prel t u)
  (#k: Ghost.erased SB.parser_kind) (#p: LowParse.Tot.Base.parser k u)
  (f: aparser #t #u r #(Ghost.reveal k) p)
  (g: u -> bool)
: aparser #t #(LowParse.Spec.Combinators.parse_filter_refine g) (prel_refine #t #u r g) #(LowParse.Spec.Combinators.parse_filter_kind k) (LowParse.Tot.Combinators.parse_filter p g)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  LowParse.Tot.Combinators.parse_filter_eq p g w;
  let res = f input #pm #w #(Ghost.hide (Ghost.reveal v <: u));
  rewrite each (r pm res (Ghost.reveal v <: u)) as (prel_refine r g pm res v);
  res
}
