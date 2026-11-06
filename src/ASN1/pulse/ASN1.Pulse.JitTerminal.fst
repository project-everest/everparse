module ASN1.Pulse.JitTerminal
#lang-pulse

(* Checks on the raw input of a terminal, before writing it: a DER content
   is valid (`L.tacc`), satisfies a restriction, or differs from a DEFAULT
   value (`L.holds`). Small integers are checked arithmetically; slices
   are validated in place. No scratch buffer and no allocation. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Sequence
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel
open ASN1.Spec.Content.Enc

open Pulse.Lib.Slice { ( .() ) }
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I64 = FStar.Int64
module Cast = FStar.Int.Cast
module SB = LowParse.Spec.Base
module LPS = LowParse.Pulse.Base
module W = LowParse.Pulse.R2L
module E = ASN1.Spec.Content.Enc
module INT = ASN1.Spec.Content.INTEGER
module In = ASN1.Pulse.Interpreter
module Rs = ASN1.Pulse.Restrict
module C = ASN1.Pulse.Checkers
module Term = ASN1.Pulse.Terminal
module ADB = ASN1.Pulse.AnyDefinedBy
module L = ASN1.Pulse.JitWriter.Lemmas
module BS = ASN1.Spec.Content.BITSTRING

(* Exact pre-checker of `r pm x' x` against `a x`, assuming `g x` *)
inline_for_extraction
let pcg (#t: Type0) (r: bprel t) (g a: SB.bytes -> prop) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  stt bool (r pm x' x ** pure (g x)) (fun res -> r pm x' x ** pure (res == true <==> a x))

let ptrue (_: SB.bytes) : prop = True

(* Pure helpers and lemmas *)

let slice_full (w: SB.bytes) : Lemma (Seq.slice w 0 (Seq.length w) == w) =
  Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length w)) w

let acc_of_valid (#k: SB.parser_kind) (#t: Type) (p: SB.parser k t) (w: SB.bytes) (off: SZ.t)
: Lemma (requires (LPS.validator_postcond p 0sz w off true /\ SZ.v off == Seq.length w))
  (ensures (L.acc p w))
= slice_full w

let valid_iff (#k: SB.parser_kind) (#t: Type) (p: SB.parser k t) (w: SB.bytes) (off: SZ.t) (valid: bool)
: Lemma (requires (LPS.validator_postcond p 0sz w off valid))
  (ensures ((valid && (SZ.v off = Seq.length w)) == true <==> L.acc p w))
= slice_full w

let none_of_invalid (#k: SB.parser_kind) (#t: Type) (p: SB.parser k t) (w: SB.bytes) (off: SZ.t)
: Lemma (requires (LPS.validator_postcond p 0sz w off false))
  (ensures (None? (SB.parse p w)))
= slice_full w

(* 64-bit integers *)

let i64_tacc (bound: pos) (i: I64.t) (f: asn1_terminal_t (ASN1_INTEGER bound) -> bool)
: Lemma (requires (INT.interval bound (I64.v i)))
  (ensures (L.tacc (ASN1_INTEGER bound) (i64_enc i) /\
    (L.holds (ASN1_INTEGER bound) f (i64_enc i) <==> f (I64.v i) == true)))
= let x : asn1_terminal_t (ASN1_INTEGER bound) = I64.v i in
  assert (E.leaf_enc (ASN1_INTEGER bound) x == i64_enc i);
  L.leaf_tacc (ASN1_INTEGER bound) x f (i64_enc i)

let i64_interval (bound: pos) (i: I64.t)
: Lemma (requires (bound <= 8 /\ L.tacc (ASN1_INTEGER bound) (i64_enc i)))
  (ensures (INT.interval bound (I64.v i)))
= L.i64_interval bound (I64.v i) (i64_enc i)

let i64_big (bound: pos) (i: I64.t)
: Lemma (requires (bound >= 8)) (ensures (INT.interval bound (I64.v i)))
= INT.interval_weaken 8 bound (I64.v i)

(* `i` fits in `bound` bytes; `bound` is a constant of the schema *)
[@@In.asn1_pulse_attr]
inline_for_extraction
let i64_lim (bound: pos { bound < 8 }) : Tot I64.t =
  if bound = 1 then 128L
  else if bound = 2 then 32768L
  else if bound = 3 then 8388608L
  else if bound = 4 then 2147483648L
  else if bound = 5 then 549755813888L
  else if bound = 6 then 140737488355328L
  else 36028797018963968L

let i64_lim_correct (bound: pos { bound < 8 })
: Lemma (I64.v (i64_lim bound) == pow2 (8 * bound - 1))
= assert_norm (pow2 7 == 128);
  assert_norm (pow2 15 == 32768);
  assert_norm (pow2 23 == 8388608);
  assert_norm (pow2 31 == 2147483648);
  assert_norm (pow2 39 == 549755813888);
  assert_norm (pow2 47 == 140737488355328);
  assert_norm (pow2 55 == 36028797018963968)

[@@In.asn1_pulse_attr]
inline_for_extraction
let i64_fits (bound: pos { bound <= 8 }) (i: I64.t) : Tot bool =
  if bound >= 8 then true
  else begin
    let lim = i64_lim bound in
    I64.lte (I64.sub 0L lim) i && I64.lt i lim
  end

let i64_fits_correct (bound: pos { bound <= 8 }) (i: I64.t)
: Lemma (i64_fits bound i == true <==> INT.interval bound (I64.v i))
= if bound >= 8 then i64_big bound i
  else i64_lim_correct bound

(* Sign and magnitude, as expected by the restriction checks *)
inline_for_extraction
let i64_mag (i: I64.t) : Tot U64.t =
  if I64.lt i 0L
  then U64.add (Cast.int64_to_uint64 (I64.sub (I64.sub 0L 1L) i)) 1UL
  else Cast.int64_to_uint64 i

let i64_mag_correct (i: I64.t)
: Lemma (Rs.int_view_ok (I64.lt i 0L) false (i64_mag i) (I64.v i))
= ()

let int_pred_restriction (bound: pos) (r: asn1_restriction (ASN1_INTEGER bound) { Rs.int_restriction_ok r }) (x: asn1_terminal_t (ASN1_INTEGER bound))
: Lemma (restriction_pred r x == Rs.int_pred r x)
= ()

inline_for_extraction
let i64_restr (#bound: pos) (r: asn1_restriction (ASN1_INTEGER bound) { Rs.int_restriction_ok r }) (i: I64.t) : Tot bool =
  Rs.int_check r (I64.lt i 0L) false (i64_mag i)

let i64_restr_correct (#bound: pos) (r: asn1_restriction (ASN1_INTEGER bound) { Rs.int_restriction_ok r }) (i: I64.t)
: Lemma (i64_restr r i == Rs.int_pred r (I64.v i))
= i64_mag_correct i;
  Rs.int_check_correct r (I64.lt i 0L) false (i64_mag i) (I64.v i)

(* Comparison of a 64-bit integer with an INTEGER literal *)

let lv (a: int) (l: list U8.t) : GTot int = a * pow2 (8 * List.Tot.length l) + be_of_list l

let rec be_of_list_bound (l: list U8.t)
: Lemma (be_of_list l < pow2 (8 * List.Tot.length l))
= match l with
  | [] -> ()
  | c :: q ->
    be_of_list_bound q;
    FStar.Math.Lemmas.pow2_plus 8 (8 * List.Tot.length q);
    FStar.Math.Lemmas.lemma_mult_le_right (pow2 (8 * List.Tot.length q)) (U8.v c) 255

let i55 : I64.t = 36028797018963968L

[@@In.asn1_pulse_attr]
let rec lit_cmp (i: I64.t) (a: I64.t) ([@@@FStar.Attributes.monomorphize] l: list U8.t) : Tot bool (decreases l) =
  match l with
  | [] -> I64.eq i a
  | c :: q ->
    if I64.lte (I64.sub 0L i55) a && I64.lt a i55
    then begin
      assert_norm (I64.v i55 == pow2 55);
      assert_norm (pow2 63 == 256 * pow2 55);
      lit_cmp i (I64.add (I64.mul a 256L) (Cast.uint8_to_int64 c)) q
    end
    else false

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec lit_cmp_correct (i: I64.t) (a: I64.t) (l: list U8.t)
: Lemma (ensures (lit_cmp i a l == (I64.v i = lv (I64.v a) l))) (decreases l)
= match l with
  | [] -> ()
  | c :: q ->
    let n = 8 * List.Tot.length q in
    FStar.Math.Lemmas.pow2_plus 8 n;
    assert_norm (I64.v i55 == pow2 55);
    assert_norm (pow2 63 == 256 * pow2 55);
    assert_norm (pow2 8 == 256);
    be_of_list_bound q;
    if I64.v a >= 0 - pow2 55 && I64.v a < pow2 55
    then begin
      let a' = I64.add (I64.mul a 256L) (Cast.uint8_to_int64 c) in
      lit_cmp_correct i a' q;
      assert (I64.v a' == I64.v a * 256 + U8.v c);
      FStar.Math.Lemmas.distributivity_add_left (I64.v a * 256) (U8.v c) (pow2 n);
      FStar.Math.Lemmas.paren_mul_right (I64.v a) 256 (pow2 n)
    end else begin
      FStar.Math.Lemmas.pow2_le_compat n 0;
      FStar.Math.Lemmas.pow2_plus 55 (8 + n);
      FStar.Math.Lemmas.pow2_le_compat (55 + 8 + n) 63;
      if I64.v a >= pow2 55
      then FStar.Math.Lemmas.lemma_mult_le_right (pow2 (8 + n)) (pow2 55) (I64.v a)
      else FStar.Math.Lemmas.lemma_mult_le_right (pow2 (8 + n)) (I64.v a) (0 - pow2 55 - 1)
    end
#pop-options

[@@In.asn1_pulse_attr]
inline_for_extraction
let lit_eq (i: I64.t) ([@@@FStar.Attributes.monomorphize] l: list U8.t) : Tot bool =
  match l with
  | [] -> I64.eq i 0L
  | c0 :: q ->
    lit_cmp i (if U8.gte c0 128uy then I64.sub (Cast.uint8_to_int64 c0) 256L else Cast.uint8_to_int64 c0) q

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"
let lit_eq_correct (i: I64.t) (l: list U8.t)
: Lemma (lit_eq i l == (I64.v i = int_of_lit_list l))
= match l with
  | [] -> ()
  | c0 :: q ->
    let a0 : I64.t = if U8.gte c0 128uy then I64.sub (Cast.uint8_to_int64 c0) 256L else Cast.uint8_to_int64 c0 in
    lit_cmp_correct i a0 q;
    FStar.Math.Lemmas.pow2_plus 8 (8 * List.Tot.length q);
    assert_norm (pow2 8 == 256);
    FStar.Math.Lemmas.distributivity_sub_left (U8.v c0) 256 (pow2 (8 * List.Tot.length q))
#pop-options

let int_lit_val (bound: pos) (l: asn1_int_lit bound)
: Lemma (key_of_lit (ASN1_INTEGER bound) l == int_of_lit_list l)
= int_of_lit_list_correct bound l

(* BIT STRING *)

let bitstring_parts (u: U8.t) (b: SB.bytes)
: Lemma (let w = Seq.append (W.enc_byte u) b in
    Seq.length w > 0 /\ Seq.index w 0 == u /\ Seq.slice w 1 (Seq.length w) == b)
= let w = Seq.append (W.enc_byte u) b in
  Seq.lemma_eq_elim (Seq.slice w 1 (Seq.length w)) b

let bitstring_tacc (u: U8.t) (b: SB.bytes)
: Lemma (requires (BS.filter_asn1_bitstring_unused u /\ BS.filter_asn1_bitstring_payload u b))
  (ensures (L.tacc ASN1_BITSTRING (Seq.append (W.enc_byte u) b)))
= let w = Seq.append (W.enc_byte u) b in
  bitstring_parts u b;
  Term.bitstring_eq w

let bitstring_tacc_iff (u: U8.t) (b: SB.bytes)
: Lemma ((BS.filter_asn1_bitstring_unused u /\ BS.filter_asn1_bitstring_payload u b) <==> L.tacc ASN1_BITSTRING (Seq.append (W.enc_byte u) b))
= let w = Seq.append (W.enc_byte u) b in
  bitstring_parts u b;
  Term.bitstring_eq w

let bitstring_eq_not_holds (defl: asn1_key_lit ASN1_BITSTRING) (u: U8.t) (b: SB.bytes)
: Lemma (requires (u == fst #U8.t #(list U8.t) defl /\ b == Seq.seq_of_list (snd #U8.t #(list U8.t) defl)))
  (ensures (~ (L.holds ASN1_BITSTRING (defaultv_filter (key_of_lit ASN1_BITSTRING defl)) (Seq.append (W.enc_byte u) b))))
= let defl' : asn1_bitstring_lit = defl in
  let w = Seq.append (W.enc_byte u) b in
  In.key_enc_list_correct ASN1_BITSTRING defl;
  Seq.lemma_seq_of_list_induction (fst defl' :: snd defl');
  bitstring_parts u b;
  let e = E.leaf_enc ASN1_BITSTRING (key_of_lit ASN1_BITSTRING defl) in
  assert (Seq.index e 0 == fst defl');
  assert (Seq.equal (Seq.slice e 1 (Seq.length e)) (Seq.seq_of_list (snd defl')));
  Seq.lemma_split e 1;
  Seq.lemma_split w 1;
  assert (Seq.equal (Seq.slice e 0 1) (Seq.slice w 0 1));
  assert (Seq.equal w e);
  L.leaf_tacc ASN1_BITSTRING (key_of_lit ASN1_BITSTRING defl) (defaultv_filter (key_of_lit ASN1_BITSTRING defl)) w

let bitstring_neq (defl: asn1_key_lit ASN1_BITSTRING) (u: U8.t) (b: SB.bytes)
: Lemma (requires (~ (u == fst #U8.t #(list U8.t) defl) \/ ~ (b == Seq.seq_of_list (snd #U8.t #(list U8.t) defl))))
  (ensures (L.holds ASN1_BITSTRING (defaultv_filter (key_of_lit ASN1_BITSTRING defl)) (Seq.append (W.enc_byte u) b)))
= let defl' : asn1_bitstring_lit = defl in
  let w = Seq.append (W.enc_byte u) b in
  In.key_enc_list_correct ASN1_BITSTRING defl;
  Seq.lemma_seq_of_list_induction (fst defl' :: snd defl');
  bitstring_parts u b;
  let e = E.leaf_enc ASN1_BITSTRING (key_of_lit ASN1_BITSTRING defl) in
  if Seq.length w = Seq.length e then begin
    assert (Seq.index e 0 == fst defl');
    assert (Seq.equal (Seq.slice e 1 (Seq.length e)) (Seq.seq_of_list (snd defl')))
  end;
  L.neq_enc_holds ASN1_BITSTRING (key_of_lit ASN1_BITSTRING defl) w

(* Per-kind lemmas *)

let pand (a1 a2: SB.bytes -> prop) (x: SB.bytes) : prop = a1 x /\ a2 x

let is_slice_leaf (k: asn1_terminal_k) : Tot bool =
  match k with
  | ASN1_BOOLEAN | ASN1_NULL | ASN1_INTEGER _ | ASN1_BITSTRING | ASN1_PREFIXED_TERMINAL _ _ -> false
  | _ -> true

#push-options "--ifuel 2 --fuel 2"
let slice_leaf_eq (k: E.leaf_k { is_slice_leaf k }) (g a: SB.bytes -> prop) (pm: perm)
: Lemma (pcg (raw_leaf k) g a pm == pcg raw_slice g a pm)
= assert (raw_leaf k == raw_slice)
#pop-options

let bool_tacc (x: bool)
: Lemma (L.tacc ASN1_BOOLEAN (boolean_enc x))
= L.leaf_tacc ASN1_BOOLEAN x (fun _ -> true) (boolean_enc x)

let null_tacc (x: unit)
: Lemma (L.tacc ASN1_NULL (null_enc x))
= assert (E.leaf_enc ASN1_NULL x == null_enc x);
  L.leaf_tacc ASN1_NULL x (fun _ -> true) (null_enc x)

let bool_restr (r: asn1_restriction ASN1_BOOLEAN { RESTRICT_IN? r }) (x: bool)
: Lemma (Rs.bool_in (RESTRICT_IN?.values r) x == true <==> L.holds ASN1_BOOLEAN (restriction_pred r) (boolean_enc x))
= Rs.bool_in_correct (RESTRICT_IN?.values r) x;
  L.leaf_tacc ASN1_BOOLEAN x (restriction_pred r) (boolean_enc x)

let bool_neq (defl: asn1_key_lit ASN1_BOOLEAN) (x: bool)
: Lemma (not (x = (defl <: bool)) == true <==> L.holds ASN1_BOOLEAN (defaultv_filter (key_of_lit ASN1_BOOLEAN defl)) (boolean_enc x))
= assert (key_of_lit ASN1_BOOLEAN defl == defl);
  L.leaf_tacc ASN1_BOOLEAN x (defaultv_filter (key_of_lit ASN1_BOOLEAN defl)) (boolean_enc x)

let tacc_interval (bound: pos) (i: I64.t)
: Lemma (requires (L.tacc (ASN1_INTEGER bound) (i64_enc i))) (ensures (INT.interval bound (I64.v i)))
= if bound <= 8 then i64_interval bound i else i64_big bound i

let i64_valid (bound: pos { bound <= 8 }) (i: I64.t)
: Lemma (i64_fits bound i == true <==> L.tacc (ASN1_INTEGER bound) (i64_enc i))
= i64_fits_correct bound i;
  if i64_fits bound i then i64_tacc bound i (fun _ -> true)
  else Classical.move_requires (tacc_interval bound) i

let small_valid (bound: pos { bound > 8 }) (i: I64.t)
: Lemma (L.tacc (ASN1_INTEGER bound) (i64_enc i))
= i64_big bound i;
  i64_tacc bound i (fun _ -> true)

let i64_restr_holds (bound: pos) (r: asn1_restriction (ASN1_INTEGER bound) { Rs.int_restriction_ok r }) (i: I64.t)
: Lemma (requires (L.tacc (ASN1_INTEGER bound) (i64_enc i)))
  (ensures (i64_restr r i == true <==> L.holds (ASN1_INTEGER bound) (restriction_pred r) (i64_enc i)))
= tacc_interval bound i;
  i64_restr_correct r i;
  int_pred_restriction bound r (I64.v i);
  i64_tacc bound i (restriction_pred r)

let i64_neq_holds (bound: pos) (defl: asn1_key_lit (ASN1_INTEGER bound)) (i: I64.t)
: Lemma (requires (L.tacc (ASN1_INTEGER bound) (i64_enc i)))
  (ensures (not (lit_eq i defl) == true <==> L.holds (ASN1_INTEGER bound) (defaultv_filter (key_of_lit (ASN1_INTEGER bound) defl)) (i64_enc i)))
= tacc_interval bound i;
  lit_eq_correct i defl;
  int_lit_val bound defl;
  i64_tacc bound i (defaultv_filter (key_of_lit (ASN1_INTEGER bound) defl))

let null_neq (defl: asn1_key_lit ASN1_NULL) (x: unit)
: Lemma (~ (L.holds ASN1_NULL (defaultv_filter (key_of_lit ASN1_NULL defl)) (null_enc x)))
= assert (E.leaf_enc ASN1_NULL x == null_enc x);
  L.leaf_tacc ASN1_NULL x (defaultv_filter (key_of_lit ASN1_NULL defl)) (null_enc x)

(* Combinators *)

inline_for_extraction
fn pc_then (#t: Type0) (r: bprel t) (g a1 g2 a2: SB.bytes -> prop)
  (imp: (x: SB.bytes) -> Lemma (requires (g x /\ a1 x)) (ensures (g2 x)))
  (pm: perm) (c1: pcg r g a1 pm) (c2: pcg r g2 a2 pm)
: pcg #t r g (pand a1 a2) pm
= (x': t) (#x: Ghost.erased SB.bytes)
{
  let ok = c1 x' #x;
  if ok {
    imp x;
    c2 x' #x
  } else {
    false
  }
}

inline_for_extraction
fn pc_pure (#t: Type0) (enc: t -> GTot SB.bytes) (g a: SB.bytes -> prop) (f: t -> bool)
  (lem: (x': t) -> Lemma (requires (g (enc x'))) (ensures (f x' == true <==> a (enc x'))))
  (pm: perm)
: pcg #t (raw_pure enc) g a pm
= (x': t) (#x: Ghost.erased SB.bytes)
{
  unfold (raw_pure enc pm x' x);
  fold (raw_pure enc pm x' x);
  lem x';
  f x'
}

inline_for_extraction
fn pc_slice (#tp: Type0) (#kk: Ghost.erased SB.parser_kind) (#pp: SB.parser kk tp) (vf: LPS.validator pp)
  (g a: SB.bytes -> prop)
  (lem: (w: SB.bytes) -> Lemma (requires (g w)) (ensures (L.acc pp w <==> a w)))
  (pm: perm)
: pcg raw_slice g a pm
= (s: S.slice U8.t) (#x: Ghost.erased SB.bytes)
{
  unfold (raw_slice pm s x);
  unfold (prel_slice_ser id_enc pm s x);
  with w . assert (S.pts_to s #pm w);
  S.pts_to_len s;
  let mut off = 0sz;
  let valid = vf s off;
  let off1 = !off;
  fold (prel_slice_ser id_enc pm s x);
  fold (raw_slice pm s x);
  valid_iff pp w off1 valid;
  lem x;
  (valid && (off1 = S.len s))
}

inline_for_extraction
fn pc_int (g a: SB.bytes -> prop) (f: I64.t -> bool)
  (lem: (i: I64.t) -> Lemma (requires (g (i64_enc i))) (ensures (f i == true <==> a (i64_enc i))))
  (pm: perm) (cs: pcg raw_slice g a pm)
: pcg #asn1_int_impl raw_int g a pm
= (x': asn1_int_impl) (#x: Ghost.erased SB.bytes)
{
  match x' {
    Small i -> {
      rewrite (raw_int pm x' x) as (pure (Ghost.reveal x == i64_enc i));
      rewrite (pure (Ghost.reveal x == i64_enc i)) as (raw_int pm x' x);
      lem i;
      f i
    }
    Big s -> {
      rewrite (raw_int pm x' x) as (raw_slice pm s x);
      let res = cs s #x;
      rewrite (raw_slice pm s x) as (raw_int pm x' x);
      res
    }
  }
}

(* DEFAULT value of a slice-backed terminal: compare against the literal *)
inline_for_extraction
fn pn_slice (k: asn1_terminal_k) (u: squash (In.adb_key_supported k)) (defl: asn1_key_lit k) (g: SB.bytes -> prop) (pm: perm)
: pcg raw_slice g (L.holds k (defaultv_filter (key_of_lit k defl))) pm
= (s: S.slice U8.t) (#x: Ghost.erased SB.bytes)
{
  unfold (raw_slice pm s x);
  unfold (prel_slice_ser id_enc pm s x);
  with w . assert (S.pts_to s #pm w);
  S.pts_to_len s;
  let mut off = 0sz;
  let valid = In.validate_key_eq_fl k () defl (S.len s) s off;
  let off1 = !off;
  fold (prel_slice_ser id_enc pm s x);
  fold (raw_slice pm s x);
  slice_full w;
  if valid {
    L.fl_eq_not_holds k (key_of_lit k defl) w;
    false
  } else {
    L.neq_fl_holds k (key_of_lit k defl) w;
    true
  }
}

(* BIT STRING, from its parts *)

fn check_bits (u: U8.t) (s: S.slice U8.t) (#pm: perm) (#b: Ghost.erased SB.bytes)
requires S.pts_to s #pm b
returns res: bool
ensures S.pts_to s #pm b ** pure (res == true <==> (BS.filter_asn1_bitstring_unused u /\ BS.filter_asn1_bitstring_payload u b))
{
  S.pts_to_len s;
  if (U8.lte u 7uy) {
    if (u = 0uy) {
      true
    } else {
      let len = S.len s;
      if (len = 0sz) {
        false
      } else {
        let last = s.(SZ.sub len 1sz);
        C.bitstring_mask_lemma u last;
        (U8.rem last (U8.shift_left 1uy (Cast.uint8_to_uint32 u)) = 0uy)
      }
    }
  } else {
    false
  }
}

inline_for_extraction
fn pv_bitstring (g: SB.bytes -> prop) (pm: perm)
: pcg #asn1_bitstring_impl raw_bitstring g (L.tacc ASN1_BITSTRING) pm
= (x': asn1_bitstring_impl) (#x: Ghost.erased SB.bytes)
{
  unfold (raw_bitstring pm x' x);
  with b . assert (S.pts_to x'.bytes #pm b);
  let res = check_bits x'.unused x'.bytes;
  fold (raw_bitstring pm x' x);
  bitstring_tacc_iff x'.unused b;
  res
}

(* Projections of a BIT STRING literal: a Pulse local holding the literal
   would need a C representation of its list *)
[@@In.asn1_pulse_attr]
inline_for_extraction
let lit_unused (defl: asn1_key_lit ASN1_BITSTRING) : Tot U8.t =
  let d : asn1_bitstring_lit = defl in fst d

[@@In.asn1_pulse_attr]
inline_for_extraction
let lit_bytes (defl: asn1_key_lit ASN1_BITSTRING) : Tot (list U8.t) =
  let d : asn1_bitstring_lit = defl in snd d

inline_for_extraction
fn pn_bitstring (defl: asn1_key_lit ASN1_BITSTRING) (g: SB.bytes -> prop) (pm: perm)
: pcg #asn1_bitstring_impl raw_bitstring g (L.holds ASN1_BITSTRING (defaultv_filter (key_of_lit ASN1_BITSTRING defl))) pm
= (x': asn1_bitstring_impl) (#x: Ghost.erased SB.bytes)
{
  unfold (raw_bitstring pm x' x);
  with b . assert (S.pts_to x'.bytes #pm b);
  if (x'.unused <> lit_unused defl) {
    fold (raw_bitstring pm x' x);
    bitstring_neq defl x'.unused b;
    true
  } else {
    let mut off = 0sz;
    let valid = In.validate_bytes_eq (lit_bytes defl) x'.bytes off;
    let off1 = !off;
    fold (raw_bitstring pm x' x);
    if valid {
      ADB.bytes_eq_consumed (lit_bytes defl) b;
      slice_full b;
      bitstring_eq_not_holds defl x'.unused b;
      false
    } else {
      none_of_invalid (ADB.bytes_eq_p (lit_bytes defl)) b off1;
      ADB.bytes_eq_consumed (lit_bytes defl) b;
      bitstring_neq defl x'.unused b;
      true
    }
  }
}

(* Dispatch on the kind of the terminal *)

[@@In.asn1_pulse_attr]
inline_for_extraction
let pv_integer (bound: pos) (u: squash (In.supported_terminal (ASN1_INTEGER bound))) (pm: perm)
: pcg (raw_integer bound) ptrue (L.tacc (ASN1_INTEGER bound)) pm
= if small_integer bound
  then coerce_eq () (pc_pure i64_enc ptrue (L.tacc (ASN1_INTEGER bound)) (i64_fits bound) (i64_valid bound) pm)
  else coerce_eq () (pc_int ptrue (L.tacc (ASN1_INTEGER bound)) (fun _ -> true) (fun i -> small_valid bound i) pm
    (pc_slice (In.validate_terminal (ASN1_INTEGER bound) ()) ptrue (L.tacc (ASN1_INTEGER bound)) (fun _ -> ()) pm))

[@@In.asn1_pulse_attr]
inline_for_extraction
let pv (k: E.leaf_k) (u: squash (In.supported_terminal k)) (pm: perm)
: pcg (raw_leaf k) ptrue (L.tacc k) pm
= match k with
  | ASN1_BOOLEAN -> pc_pure boolean_enc ptrue (L.tacc ASN1_BOOLEAN) (fun _ -> true) bool_tacc pm
  | ASN1_NULL -> pc_pure null_enc ptrue (L.tacc ASN1_NULL) (fun _ -> true) null_tacc pm
  | ASN1_INTEGER bound -> pv_integer bound () pm
  | ASN1_BITSTRING -> pv_bitstring ptrue pm
  | _ ->
    slice_leaf_eq k ptrue (L.tacc k) pm;
    coerce_eq () (pc_slice (In.validate_terminal k ()) ptrue (L.tacc k) (fun _ -> ()) pm)

[@@In.asn1_pulse_attr]
inline_for_extraction
let pr_integer (bound: pos) (r: asn1_restriction (ASN1_INTEGER bound)) (u: squash (In.supported_restriction (ASN1_INTEGER bound) r)) (pm: perm)
: pcg (raw_integer bound) (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (restriction_pred r)) pm
= if small_integer bound
  then coerce_eq () (pc_pure i64_enc (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (restriction_pred r)) (i64_restr r) (i64_restr_holds bound r) pm)
  else coerce_eq () (pc_int (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (restriction_pred r)) (i64_restr r) (i64_restr_holds bound r) pm
    (pc_slice (In.validate_restricted (ASN1_INTEGER bound) r ()) (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (restriction_pred r)) (fun w -> L.restricted_iff (ASN1_INTEGER bound) r w) pm))

[@@In.asn1_pulse_attr]
inline_for_extraction
let pr (k: E.leaf_k) (r: asn1_restriction k) (u: squash (In.supported_restriction k r)) (pm: perm)
: pcg (raw_leaf k) (L.tacc k) (L.holds k (restriction_pred r)) pm
= match k with
  | ASN1_BOOLEAN -> pc_pure boolean_enc (L.tacc ASN1_BOOLEAN) (L.holds ASN1_BOOLEAN (restriction_pred r)) (Rs.bool_in (RESTRICT_IN?.values r)) (bool_restr r) pm
  | ASN1_INTEGER bound -> pr_integer bound r () pm
  | _ ->
    slice_leaf_eq k (L.tacc k) (L.holds k (restriction_pred r)) pm;
    coerce_eq () (pc_slice (In.validate_restricted k r ()) (L.tacc k) (L.holds k (restriction_pred r)) (fun w -> L.restricted_iff k r w) pm)

[@@In.asn1_pulse_attr]
inline_for_extraction
let pn_integer (bound: pos) (defl: asn1_key_lit (ASN1_INTEGER bound)) (u: squash (In.adb_key_supported (ASN1_INTEGER bound))) (pm: perm)
: pcg (raw_integer bound) (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (defaultv_filter (key_of_lit (ASN1_INTEGER bound) defl))) pm
= if small_integer bound
  then coerce_eq () (pc_pure i64_enc (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (defaultv_filter (key_of_lit (ASN1_INTEGER bound) defl))) (fun i -> not (lit_eq i defl)) (i64_neq_holds bound defl) pm)
  else coerce_eq () (pc_int (L.tacc (ASN1_INTEGER bound)) (L.holds (ASN1_INTEGER bound) (defaultv_filter (key_of_lit (ASN1_INTEGER bound) defl))) (fun i -> not (lit_eq i defl)) (i64_neq_holds bound defl) pm
    (pn_slice (ASN1_INTEGER bound) () defl (L.tacc (ASN1_INTEGER bound)) pm))

[@@In.asn1_pulse_attr]
inline_for_extraction
let pn (k: E.leaf_k) (defl: asn1_key_lit k) (u: squash (In.adb_key_supported k)) (pm: perm)
: pcg (raw_leaf k) (L.tacc k) (L.holds k (defaultv_filter (key_of_lit k defl))) pm
= match k with
  | ASN1_BOOLEAN -> pc_pure boolean_enc (L.tacc ASN1_BOOLEAN) (L.holds ASN1_BOOLEAN (defaultv_filter (key_of_lit ASN1_BOOLEAN defl))) (fun x -> not (x = (defl <: bool))) (bool_neq defl) pm
  | ASN1_NULL -> pc_pure null_enc (L.tacc ASN1_NULL) (L.holds ASN1_NULL (defaultv_filter (key_of_lit ASN1_NULL defl))) (fun _ -> false) (null_neq defl) pm
  | ASN1_INTEGER bound -> pn_integer bound defl () pm
  | ASN1_BITSTRING -> pn_bitstring defl (L.tacc ASN1_BITSTRING) pm
  | _ ->
    slice_leaf_eq k (L.tacc k) (L.holds k (defaultv_filter (key_of_lit k defl))) pm;
    coerce_eq () (pn_slice k () defl (L.tacc k) pm)
