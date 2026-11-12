module ASN1.Pulse.WriteLeaf
#lang-pulse

(* Right-to-left writers (`LowParse.Pulse.R2L`) for the leaves of ASN.1 DER
   encodings: identifiers, length headers, TLV framing, and the contents of
   terminal types, from the Pulse representations of `ASN1.Pulse.Rel`. *)

open Pulse.Lib.Pervasives
open LowParse.Pulse.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Spec.ToValue
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I64 = FStar.Int64
module Cast = FStar.Int.Cast
module W = LowParse.Pulse.R2L
module SB = LowParse.Spec.Base
module INT = ASN1.Spec.Content.INTEGER
module LE = LowParse.Endianness
module DER = LowParse.Pulse.DER
module Conf = ASN1.Spec.Conformance

(* Identifiers (X.690 8.1.2) *)

let id_b (v: asn1_partial_id_t) (m: nat { m <= id_bound v }) : Tot nat =
  id_digit v m + (if m < id_bound v then 128 else 0)

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"
let rec enc_tail_index (v: asn1_partial_id_t) (i: nat { i < id_bound v })
: Lemma
  (ensures (Seq.length (enc_tail v i) == id_bound v - i /\
    (forall (k: nat) . k < id_bound v - i ==> U8.v (Seq.index (enc_tail v i) k) == id_b v (i + 1 + k))))
  (decreases (id_bound v - i))
= let m = i + 1 in
  if m = id_bound v then () else enc_tail_index v m
#pop-options

let cons_index (x: U8.t) (s: Seq.seq U8.t)
: Lemma (Seq.length (Seq.cons x s) == Seq.length s + 1 /\
    Seq.index (Seq.cons x s) 0 == x /\
    (forall (k: nat { 0 < k /\ k <= Seq.length s }) . Seq.index (Seq.cons x s) k == Seq.index s (k - 1)))
= let prf (k: nat { 0 < k /\ k <= Seq.length s }) : Lemma (Seq.index (Seq.cons x s) k == Seq.index s (k - 1)) =
    Seq.index_cons_r x s k
  in
  Classical.forall_intro prf

let enc_long_index (v: U32.t { 31 <= U32.v v })
: Lemma (Seq.length (enc_long v) == id_bound v + 1 /\
    (forall (k: nat) . k <= id_bound v ==> U8.v (Seq.index (enc_long v) k) == id_b v k))
= if id_bound v = 0
  then begin
    id_digit_last v;
    assert_norm (pow2 7 == 128)
  end
  else begin
    enc_tail_index v 0;
    cons_index (U8.uint_to_t (id_digit v 0 + 128)) (enc_tail v 0)
  end

let id_len_spec (id: asn1_id_t) : Tot nat =
  if U32.v id.v < 31 then 1 else id_bound id.v + 2

let first_byte_spec (id: asn1_id_t) : Tot nat =
  64 * id_class_num id.c + 32 * id_flag_num id.f + (if U32.v id.v < 31 then U32.v id.v else 31)

let id_byte_spec (id: asn1_id_t) (i: nat { i < id_len_spec id }) : Tot nat =
  if i = 0 then first_byte_spec id else id_b id.v (i - 1)

let asn1_id_enc_index_short (id: asn1_id_t)
: Lemma (requires U32.v id.v < 31)
  (ensures (let e = asn1_id_enc id in
    Seq.length e == 1 /\ U8.v (Seq.index e 0) == first_byte_spec id))
= let b = Cast.uint32_to_uint8 id.v in
  FStar.Math.Lemmas.small_mod (U32.v id.v) (pow2 8);
  assert (U8.v b == U32.v id.v);
  encode_asn1_first_byte_value id.c id.f b;
  let e = encode_asn1_first_byte id.c id.f b in
  assert (asn1_id_enc id == Seq.create 1 e)

#push-options "--fuel 0 --ifuel 0"
let asn1_id_enc_index_short_all (id: asn1_id_t)
: Lemma (requires U32.v id.v < 31)
  (ensures Seq.length (asn1_id_enc id) == id_len_spec id /\
    (forall (i: nat) . i < id_len_spec id ==> U8.v (Seq.index (asn1_id_enc id) i) == id_byte_spec id i))
= asn1_id_enc_index_short id;
  assert (id_len_spec id == 1);
  assert (id_byte_spec id 0 == first_byte_spec id)
#pop-options

let asn1_id_enc_index (id: asn1_id_t)
: Lemma (Seq.length (asn1_id_enc id) == id_len_spec id /\
    (forall (i: nat) . i < id_len_spec id ==> U8.v (Seq.index (asn1_id_enc id) i) == id_byte_spec id i))
= let c = id.c in
  let f = id.f in
  let n = id.v in
  if U32.v n < 31
  then begin
    asn1_id_enc_index_short_all id
  end
  else begin
    assert (U8.v 31uy == 31);
    encode_asn1_first_byte_value c f 31uy;
    enc_long_index n;
    let e = encode_asn1_first_byte c f 31uy in
    assert (asn1_id_enc id == Seq.cons e (enc_long n));
    cons_index e (enc_long n);
    assert (id_len_spec id == id_bound n + 2);
    let prf (i: nat) : Lemma (i < id_len_spec id ==> U8.v (Seq.index (asn1_id_enc id) i) == id_byte_spec id i) =
      if i = 0 then () else if i < id_len_spec id then assert (id_byte_spec id i == id_b n (i - 1)) else ()
    in
    Classical.forall_intro prf
  end

inline_for_extraction
let rt_bound (v: U32.t { 31 <= U32.v v }) : Tot (j: U32.t { U32.v j == id_bound v }) =
  assert_norm (pow2 0 == 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 14 == 16384);
  assert_norm (pow2 21 == 2097152);
  assert_norm (pow2 28 == 268435456);
  assert_norm (pow2 35 == 34359738368);
  if U32.lt v 128ul then (lemma_partial_state_bound_f32_intro v 0; 0ul)
  else if U32.lt v 16384ul then (lemma_partial_state_bound_f32_intro v 1; 1ul)
  else if U32.lt v 2097152ul then (lemma_partial_state_bound_f32_intro v 2; 2ul)
  else if U32.lt v 268435456ul then (lemma_partial_state_bound_f32_intro v 3; 3ul)
  else (lemma_partial_state_bound_f32_intro v 4; 4ul)

#push-options "--fuel 0 --ifuel 0"
let rt_digit_lemma (v: U32.t { 31 <= U32.v v }) (j: nat) (m: nat) (q: U32.t)
: Lemma
  (requires (j == id_bound v /\ m <= j /\ U32.v q == U32.v v / pow2 (7 * (j - m))))
  (ensures (U32.v (U32.rem q 128ul) == id_digit v m))
= lemma_partial_state_prefixf_val v m;
  FStar.Math.Lemmas.swap_mul (j - m) 7
#pop-options

inline_for_extraction
let rt_id_b (v: U32.t { 31 <= U32.v v }) (m: U32.t { U32.v m <= id_bound v })
: Tot (b: U8.t { U8.v b == id_b v (U32.v m) })
= let j = rt_bound v in
  let q = U32.shift_right v (U32.mul 7ul (U32.sub j m)) in
  rt_digit_lemma v (U32.v j) (U32.v m) q;
  let r = U32.rem q 128ul in
  assert (U32.v r == id_digit v (U32.v m));
  assert_norm (pow2 8 == 256);
  FStar.Math.Lemmas.small_mod (U32.v r) (pow2 8);
  let d = Cast.uint32_to_uint8 r in
  assert (U8.v d == id_digit v (U32.v m));
  if U32.lt m j then U8.add d 128uy else d

inline_for_extraction
let rt_first_byte (id: asn1_id_t) : Tot (b: U8.t { U8.v b == first_byte_spec id }) =
  let c : U8.t = match id.c with
    | UNIVERSAL -> 0uy
    | APPLICATION -> 64uy
    | CONTEXT_SPECIFIC -> 128uy
    | PRIVATE -> 192uy
  in
  let f : U8.t = match id.f with
    | PRIMITIVE -> 0uy
    | CONSTRUCTED -> 32uy
  in
  let n : U8.t = if U32.lt id.v 31ul then Cast.uint32_to_uint8 id.v else 31uy in
  U8.add (U8.add c f) n

inline_for_extraction
let rt_id_len (id: asn1_id_t) : Tot (n: SZ.t { SZ.v n == id_len_spec id }) =
  if U32.lt id.v 31ul
  then 1sz
  else SZ.add (SZ.uint16_to_sizet (Cast.uint32_to_uint16 (rt_bound id.v))) 2sz

inline_for_extraction
let rt_id_byte (id: asn1_id_t) (i: SZ.t { SZ.v i < id_len_spec id })
: Tot (b: U8.t { U8.v b == id_byte_spec id (SZ.v i) })
= if SZ.eq i 0sz
  then rt_first_byte id
  else begin
    let m = SZ.sizet_to_uint32 (SZ.sub i 1sz) in
    assert_norm (pow2 32 == 4294967296);
    assert (U32.v m == SZ.v i - 1);
    rt_id_b id.v m
  end

let asn1_id_enc_index' (id: asn1_id_t) (i: nat { i < id_len_spec id })
: Lemma
  (ensures (SZ.fits i /\ i < Seq.length (asn1_id_enc id) /\ Seq.index (asn1_id_enc id) i == rt_id_byte id (SZ.uint_to_t i)))
= asn1_id_enc_index id;
  SZ.fits_at_least_16 i;
  U8.v_inj (Seq.index (asn1_id_enc id) i) (rt_id_byte id (SZ.uint_to_t i))

let asn1_id_enc_index_forall (id: asn1_id_t)
: Lemma (Seq.length (asn1_id_enc id) == id_len_spec id /\
    (forall (i: nat) . i < id_len_spec id ==> Seq.index (asn1_id_enc id) i == rt_id_byte id (SZ.uint_to_t i)))
= asn1_id_enc_index id;
  Classical.forall_intro (asn1_id_enc_index' id)

inline_for_extraction
fn r2l_write_id
  (id: asn1_id_t)
  (out: S.slice U8.t)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p: Ghost.erased SZ.t)
requires pts_to out v ** pts_to pos p ** pure (SZ.v p <= Seq.length v)
returns res: bool
ensures exists* v' p' . pts_to out v' ** pts_to pos p' ** pure (W.r2l_post (asn1_id_enc id) (SZ.v p) v res (SZ.v p') v')
{
  asn1_id_enc_index_forall id;
  W.r2l_write_indexed (rt_id_len id) (rt_id_byte id) (Ghost.hide (asn1_id_enc id)) out pos
}

(* Length headers (X.690 8.1.3). `enc_hdr ok n` is the DER length if
   `ok && n < 2^32`; otherwise (which never happens for values of
   well-formed schemas fitting in memory) it is a sequence of `n + 3` bytes
   that no DER parser accepts, which we write honestly. *)

module SDER = LowParse.Spec.DER
module LPB = LowParse.Spec.BoundedInt

let enc_len_eq_spec (y: U32.t)
: Lemma (enc_len y == SB.serialize (SDER.serialize_bounded_der_length32 0 4294967295) y)
= SDER.serialize_bounded_der_length32_unfold 0 4294967295 y;
  let x = SDER.tag_of_der_length32_impl y in
  if x `U8.lt` 128uy || x = 129uy
  then Seq.lemma_eq_elim (enc_len y) (SB.serialize (SDER.serialize_bounded_der_length32 0 4294967295) y)
  else begin
    LPB.serialize_bounded_integer_spec (LPB.log256' (U32.v y)) y;
    Seq.lemma_eq_elim (enc_len y) (SB.serialize (SDER.serialize_bounded_der_length32 0 4294967295) y)
  end

inline_for_extraction
let r2l_write_len : W.r2l_leaf_writer #(LPB.bounded_int32 0 4294967295) (SB.bare_serialize (SDER.serialize_bounded_der_length32 0 4294967295)) =
  W.r2l_leaf_writer_of_l2r (DER.l2r_leaf_write_bounded_der_length32 0 4294967295) (DER.bounded_der_length32_size 0 4294967295)

let junk_byte_spec (ok: bool) (n: nat) (i: nat) : Tot U8.t =
  if i = 0 then 0xFFuy
  else if i = 1 then (if ok then 0uy else 1uy)
  else if i = n + 2 then 0uy
  else 1uy

#push-options "--z3rlimit 32"
let enc_hdr_junk_index (ok: bool) (n: nat) (i: nat { i < n + 3 })
: Lemma
  (requires (~ (ok && n < 4294967296)))
  (ensures (Seq.length (enc_hdr ok n) == n + 3 /\ i < Seq.length (enc_hdr ok n) /\ Seq.index (enc_hdr ok n) i == junk_byte_spec ok n i))
= let a = Seq.create 1 0xFFuy in
  let b = Seq.create 1 (if ok then 0uy else 1uy) in
  let c = Seq.create n 1uy in
  let d = Seq.create 1 0uy in
  assert (enc_hdr ok n == a `Seq.append` (b `Seq.append` (c `Seq.append` d)));
  if i = 0 then ()
  else if i = 1 then ()
  else if i = n + 2 then ()
  else begin
    assert (Seq.index (c `Seq.append` d) (i - 2) == 1uy)
  end
#pop-options

let enc_hdr_junk_forall (ok: bool) (n: nat)
: Lemma
  (requires (~ (ok && n < 4294967296)))
  (ensures (Seq.length (enc_hdr ok n) == n + 3 /\
    (forall (i: nat) . i < n + 3 ==> Seq.index (enc_hdr ok n) i == junk_byte_spec ok n i)))
= Classical.forall_intro (Classical.move_requires (enc_hdr_junk_index ok n))

inline_for_extraction
let rt_junk_byte (ok: bool) (len: SZ.t) (tlen: SZ.t { SZ.v tlen == SZ.v len + 3 }) (i: SZ.t { SZ.v i < SZ.v tlen })
: Tot (b: U8.t { b == junk_byte_spec ok (SZ.v len) (SZ.v i) })
= if SZ.eq i 0sz then 0xFFuy
  else if SZ.eq i 1sz then (if ok then 0uy else 1uy)
  else if SZ.eq i (SZ.sub tlen 1sz) then 0uy
  else 1uy

inline_for_extraction
fn r2l_write_hdr (ok: bool)
: W.r2l_writer_f #SZ.t #nat W.vmatch_sz (enc_hdr ok)
= (len: SZ.t)
  (#n: Ghost.erased nat)
  (out: S.slice U8.t)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (W.vmatch_sz len n);
  fold (W.vmatch_sz len n);
  let n32 = SZ.sizet_to_uint32 len;
  assert_norm (pow2 32 == 4294967296);
  if (ok && SZ.eq (SZ.uint32_to_sizet n32) len) {
    let y : LPB.bounded_int32 0 4294967295 = n32;
    enc_len_eq_spec n32;
    fold (eq_as_slprop (LPB.bounded_int32 0 4294967295) y y);
    let res = r2l_write_len y out pos;
    unfold (eq_as_slprop (LPB.bounded_int32 0 4294967295) y y);
    res
  } else {
    enc_hdr_junk_forall ok n;
    let vp = !pos;
    if (SZ.lt vp 3sz) {
      false
    } else if (SZ.lt (SZ.sub vp 3sz) len) {
      false
    } else {
      let tlen = SZ.add len 3sz;
      W.r2l_write_indexed tlen (rt_junk_byte ok len tlen) (Ghost.hide (enc_hdr ok n)) out pos
    }
  }
}

(* TLV framing: `enc_tlv id true c`, the identifier, then the DER length of
   the contents, then the contents *)

inline_for_extraction
fn r2l_write_tlv
  (id: asn1_id_t)
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#enc: t -> GTot SB.bytes)
  (w: W.r2l_writer_f vmatch enc)
: W.r2l_writer_f #t' #t vmatch (fun x -> enc_tlv id true (enc x))
= (x': t')
  (#x: Ghost.erased t)
  (out: S.slice U8.t)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p: Ghost.erased SZ.t)
{
  let res = W.r2l_write_framed (r2l_write_hdr true) w x' out pos;
  if (res) {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let res' = r2l_write_id id out pos;
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    W.r2l_post_append (asn1_id_enc id) (W.enc_framed (enc_hdr true) enc x) (SZ.v p) v (SZ.v p1) v1 res' (SZ.v p2) v2;
    res'
  } else {
    W.r2l_post_false_weaken (W.enc_framed (enc_hdr true) enc x) (enc_tlv id true (enc x)) (SZ.v p) v (SZ.v p) v;
    false
  }
}

(* BOOLEAN, NULL *)

inline_for_extraction
fn r2l_write_boolean (pm: perm)
: W.r2l_writer_f #bool #bool (prel_eq bool pm) boolean_enc
= (x': bool)
  (#x: Ghost.erased bool)
  (out: S.slice U8.t)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p: Ghost.erased SZ.t)
{
  unfold (prel_eq bool pm x' x);
  fold (prel_eq bool pm x' x);
  let b : U8.t = (if x' then 0xFFuy else 0x00uy);
  assert (pure (Seq.equal (W.enc_byte b) (boolean_enc x)));
  fold (eq_as_slprop U8.t b b);
  let res = W.r2l_write_byte () b out pos;
  unfold (eq_as_slprop U8.t b b);
  res
}

(* INTEGER: the minimal two's complement big-endian representation *)

let int_byte_spec (n: pos) (x: int) (i: nat { i < n }) : Tot U8.t =
  U8.uint_to_t ((x % pow2 (8 * n)) / pow2 (8 * (n - 1 - i)) % 256)

#push-options "--z3rlimit 64"
let integer_enc_length (bound: pos) (x: asn1_integer_t bound)
: Lemma (Seq.length (integer_enc bound x) == INT.domain_intro_gen x)
= ()

let integer_enc_index (bound: pos) (x: asn1_integer_t bound) (i: nat { i < Seq.length (integer_enc bound x) /\ i < INT.domain_intro_gen x })
: Lemma
  (Seq.index (integer_enc bound x) i == int_byte_spec (INT.domain_intro_gen x) x i)
= let n = INT.domain_intro_gen x in
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 0 == 1);
  INT.interval_intro n x;
  FStar.Math.Lemmas.pow2_double_sum (8 * n - 1);
  if n = 1 && (x = 0 || x = -1)
  then ()
  else if x >= 0
  then begin
    FStar.Math.Lemmas.small_mod x (pow2 (8 * n));
    LE.index_n_to_be n x i
  end else begin
    FStar.Math.Lemmas.lemma_mod_plus x 1 (pow2 (8 * n));
    FStar.Math.Lemmas.small_mod (x + pow2 (8 * n)) (pow2 (8 * n));
    LE.index_n_to_be n (x + pow2 (8 * n)) i
  end
#pop-options

let integer_enc_forall (bound: pos) (x: asn1_integer_t bound) (n: SZ.t)
: Lemma
  (requires (SZ.v n == INT.domain_intro_gen x))
  (ensures (
    Seq.length (integer_enc bound x) == SZ.v n /\
    (forall (i: nat { i < Seq.length (integer_enc bound x) /\ i < SZ.v n }) . Seq.index (integer_enc bound x) i == int_byte_spec (SZ.v n) x i)))
= integer_enc_length bound x;
  Classical.forall_intro (integer_enc_index bound x)

let int_len_ok (n: pos) (x: int)
: Lemma
  (requires (INT.interval n x /\ (n = 1 \/ ~ (INT.interval (n - 1) x))))
  (ensures (INT.domain_intro_gen x == n))
= let m = INT.interval_elim n x in
  INT.interval_intro m x;
  if m < n then INT.interval_weaken m (n - 1) x;
  INT.domain_unique m (INT.domain_intro_gen x) x

inline_for_extraction
let rt_in_interval (x: I64.t) (c: I64.t) (n: Ghost.erased pos { n <= 8 /\ I64.v c == pow2 (8 * n - 1) })
: Tot (b: bool { b <==> INT.interval n (I64.v x) })
= I64.lte (I64.sub 0L c) x && I64.lt x c

#push-options "--z3rlimit 32"
inline_for_extraction
let rt_int_len (x: I64.t)
: Tot (n: SZ.t { SZ.v n == INT.domain_intro_gen (I64.v x) /\ 1 <= SZ.v n /\ SZ.v n <= 8 })
= assert_norm (pow2 7 == 128);
  assert_norm (pow2 15 == 32768);
  assert_norm (pow2 23 == 8388608);
  assert_norm (pow2 31 == 2147483648);
  assert_norm (pow2 39 == 549755813888);
  assert_norm (pow2 47 == 140737488355328);
  assert_norm (pow2 55 == 36028797018963968);
  assert_norm (pow2 63 == 9223372036854775808);
  let y = Ghost.hide (I64.v x) in
  if rt_in_interval x 128L 1 then (int_len_ok 1 y; 1sz)
  else if rt_in_interval x 32768L 2 then (int_len_ok 2 y; 2sz)
  else if rt_in_interval x 8388608L 3 then (int_len_ok 3 y; 3sz)
  else if rt_in_interval x 2147483648L 4 then (int_len_ok 4 y; 4sz)
  else if rt_in_interval x 549755813888L 5 then (int_len_ok 5 y; 5sz)
  else if rt_in_interval x 140737488355328L 6 then (int_len_ok 6 y; 6sz)
  else if rt_in_interval x 36028797018963968L 7 then (int_len_ok 7 y; 7sz)
  else (int_len_ok 8 y; 8sz)
#pop-options

let rt_int_byte_lemma (x: int) (n: pos { n <= 8 }) (i: nat { i < n })
: Lemma ((x % pow2 64) / pow2 (8 * (n - 1 - i)) % 256 == U8.v (int_byte_spec n x i))
= let k = n - 1 - i in
  let a = x % pow2 64 in
  assert_norm (pow2 8 == 256);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 x (8 * n) 64;
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 a (8 * k) (8 * n);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (a / pow2 (8 * k)) 8 (8 * n - 8 * k)

#push-options "--z3rlimit 32"
inline_for_extraction
let rt_int_byte (x: I64.t) (n: SZ.t { 1 <= SZ.v n /\ SZ.v n <= 8 }) (i: SZ.t { SZ.v i < SZ.v n })
: Tot (b: U8.t { b == int_byte_spec (SZ.v n) (I64.v x) (SZ.v i) })
= let k = SZ.sizet_to_uint32 (SZ.sub (SZ.sub n 1sz) i) in
  assert_norm (pow2 32 == 4294967296);
  let u = Cast.int64_to_uint64 x in
  assert (U64.v u == I64.v x % pow2 64);
  let sh = U32.mul 8ul k in
  assert (U32.v sh == 8 * (SZ.v n - 1 - SZ.v i));
  let s = U64.shift_right u sh in
  UInt.shift_right_value_lemma #64 (U64.v u) (U32.v sh);
  assert (U64.v s == U64.v u / pow2 (U32.v sh));
  let r = Cast.uint64_to_uint8 s in
  assert_norm (pow2 8 == 256);
  assert (U8.v r == U64.v s % 256);
  rt_int_byte_lemma (I64.v x) (SZ.v n) (SZ.v i);
  U8.v_inj r (int_byte_spec (SZ.v n) (I64.v x) (SZ.v i));
  r
#pop-options

inline_for_extraction
fn r2l_write_i64 (bound: pos) (x': I64.t) (x: Ghost.erased (asn1_integer_t bound))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
requires pts_to out v ** pts_to pos p ** pure (SZ.v p <= Seq.length v /\ I64.v x' == Ghost.reveal x)
returns res: bool
ensures exists* v' p' . pts_to out v' ** pts_to pos p' ** pure (W.r2l_post (integer_enc bound x) (SZ.v p) v res (SZ.v p') v')
{
  let n = rt_int_len x';
  integer_enc_forall bound x n;
  W.r2l_write_indexed n (rt_int_byte x' n) (Ghost.hide (integer_enc bound x)) out pos
}

(* Terminal values: the generic encoding of `terminal_to_value id k` *)

let terminal_enc (id: asn1_id_t) (k: asn1_terminal_k) (x: asn1_terminal_t k) : GTot SB.bytes =
  asn1_value_enc (terminal_to_value id k x)

let wres (#t' #t: Type0) (vmatch: t' -> t -> slprop) (enc: t -> GTot SB.bytes)
  (x': t') (x: Ghost.erased t) (out: S.slice U8.t) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t)
: Type
= stt bool
    (pts_to out v ** pts_to pos p ** vmatch x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** vmatch x' x **
       pure (W.r2l_post (enc x) (SZ.v p) v res (SZ.v p') v'))
