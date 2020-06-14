module LowParse.Spec.BitVector
open FStar.Mul

module BV = FStar.BitVector
module U8 = FStar.UInt8
module Seq = FStar.Seq

(* Big-endian conversion of a bit vector to a UInt8 *)

let rec to_uint8
  (#n: nat { n <= 8 })
  (x: BV.bv_t n)
: Tot (y: U8.t { U8.v y < pow2 n })
= if n = 0
  then 0uy
  else
    let hi = to_uint8 #(n - 1) (Seq.slice x 0 (n - 1)) in
    let hi' = hi `U8.mul` 2uy in
    let (r: U8.t { U8.v r < 2 }) = if Seq.index x (n - 1) then 1uy else 0uy in
    hi' `U8.add` r

let rec of_uint8
  (n: nat { n <= 8 })
  (x: U8.t { U8.v x < pow2 n })
: Tot (BV.bv_t n)
= if n = 0
  then Seq.empty
  else
    let hi = of_uint8 (n - 1) (x `U8.div` 2uy) in
    Seq.snoc hi (x `U8.rem` 2uy = 1uy)

#push-options "--z3rlimit 32"

let rec to_uint8_of_uint8
  (n: nat { n <= 8 })
  (x: U8.t { U8.v x < pow2 n })
: Lemma
  (to_uint8 (of_uint8 n x) == x)
= if n = 0
  then ()
  else begin
    assert (Seq.slice (of_uint8 n x) 0 (n - 1) `Seq.equal` of_uint8 (n - 1) (x `U8.div` 2uy));
    to_uint8_of_uint8 (n - 1) (x `U8.div` 2uy)
  end

let rec of_uint8_to_uint8
  (#n: nat {n <= 8})
  (x: BV.bv_t n)
: Lemma
  (of_uint8 n (to_uint8 x) `Seq.equal` x)
= if n = 0
  then ()
  else begin
    let x' = Seq.slice x 0 (n - 1) in
    of_uint8_to_uint8 #(n - 1) x' ;
    assert (
      U8.v (to_uint8 #(n - 1) x') * 2 == U8.v (to_uint8 x) \/
      U8.v (to_uint8 #(n - 1) x') * 2 + 1 == U8.v (to_uint8 x)
    );
    assert (to_uint8 #(n - 1) x' == to_uint8 x `U8.div` 2uy);
    ()
  end

#pop-options

(* parse a 8-bit vector *)

open LowParse.Spec.Combinators
open LowParse.Spec.Int

let synth_bv8 (x: U8.t) : Tot (BV.bv_t 8) =
  of_uint8 8 x

let synth_bv8_recip (x: BV.bv_t 8) : Tot U8.t =
  to_uint8 x

let synth_bv8_injective : squash (synth_injective synth_bv8) =
  synth_inverse_intro' synth_bv8_recip synth_bv8 (fun x ->
    to_uint8_of_uint8 8 x
  )

let synth_bv8_inverse : squash (synth_inverse synth_bv8 synth_bv8_recip) =
  synth_inverse_intro' synth_bv8 synth_bv8_recip (fun x ->
    of_uint8_to_uint8 x
  )

let parse_bv8_kind = parse_u8_kind

let parse_bv8 : parser parse_bv8_kind (BV.bv_t 8) =
  parse_u8 `parse_synth` synth_bv8

let serialize_bv8 : serializer parse_bv8 =
  serialize_synth
    parse_u8
    synth_bv8
    serialize_u8
    synth_bv8_recip
    ()


(* parse a 8*n bit vector *)

let synth_byte_bv (n: nat) (x: (BV.bv_t 8 & BV.bv_t (8 * n))) : Tot (BV.bv_t (8 * (1 + n))) =
  Seq.append (fst x) (snd x)

let synth_byte_bv_recip (n: nat) (x: BV.bv_t (8 * (1 + n))) : Tot (BV.bv_t 8 & BV.bv_t (8 * n)) =
  Seq.slice x 0 8, Seq.slice x 8 (Seq.length x)

let synth_byte_bv_injective (n: nat) : Lemma
  (synth_injective (synth_byte_bv n))
  [SMTPat (synth_injective (synth_byte_bv n))]
= synth_inverse_intro' (synth_byte_bv_recip n) (synth_byte_bv n) (fun x ->
    let (hd, tl) = x in
    let (hd', tl') = synth_byte_bv_recip n (synth_byte_bv n x) in
    assert (hd `Seq.equal` hd');
    assert (tl `Seq.equal` tl')
  )

let synth_byte_bv_inverse (n: nat) : Lemma
  (synth_inverse (synth_byte_bv n) (synth_byte_bv_recip n))
  [SMTPat (synth_inverse (synth_byte_bv n) (synth_byte_bv_recip n))]
= synth_inverse_intro' (synth_byte_bv n) (synth_byte_bv_recip n) (fun x ->
    assert (synth_byte_bv n (synth_byte_bv_recip n x) `Seq.equal` x)
  )

let rec parse_byte_bv_kind' (n: nat) : Tot parser_kind =
  if n = 0
  then parse_ret_kind
  else parse_bv8_kind `and_then_kind` parse_byte_bv_kind' (n - 1)

let parse_byte_bv_kind (n: nat) : Tot parser_kind =
  strong_parser_kind n n (Some ParserKindMetadataTotal)

let rec parse_byte_bv_kind_eq (n: nat) : Lemma
  (parse_byte_bv_kind n == parse_byte_bv_kind' n)
= if n = 0
  then ()
  else parse_byte_bv_kind_eq (n - 1)

let rec parse_byte_bv (n: nat) : Tot (parser (parse_byte_bv_kind n) (BV.bv_t (8 * n))) =
  parse_byte_bv_kind_eq n;
  if n = 0
  then
    parse_ret Seq.empty
  else
    (parse_bv8 `nondep_then` parse_byte_bv (n - 1)) `parse_synth` synth_byte_bv (n - 1) 

let rec serialize_byte_bv (n: nat) : Tot (serializer (parse_byte_bv n)) =
  parse_byte_bv_kind_eq n;
  if n = 0
  then
    serialize_ret Seq.empty (fun (x: BV.bv_t 0) -> assert (x `Seq.equal` Seq.empty))
  else
    serialize_synth
      (parse_bv8 `nondep_then` parse_byte_bv (n - 1))
      (synth_byte_bv (n - 1))
      (serialize_bv8 `serialize_nondep_then` serialize_byte_bv (n - 1))
      (synth_byte_bv_recip (n - 1))
      ()

(* parse extra bits (big-endian with the first bits equal to 0) *)

let extra_bytes_prop (n: nat) (x: U8.t) : Tot bool =
  U8.v x < pow2 (n % 8)

let synth_extra_bv8 (n: nat) (x: parse_filter_refine (extra_bytes_prop n)) : Tot (BV.bv_t (n % 8)) =
  of_uint8 (n % 8) x

let synth_extra_bv8_recip (n: nat) (x: BV.bv_t (n % 8)) : Tot (parse_filter_refine (extra_bytes_prop n)) =
  to_uint8 x

let synth_extra_bv8_injective (n: nat) : Lemma (synth_injective (synth_extra_bv8 n))
  [SMTPat (synth_injective (synth_extra_bv8 n))]
=
  synth_inverse_intro' (synth_extra_bv8_recip n) (synth_extra_bv8 n) (fun x ->
    to_uint8_of_uint8 (n % 8) x
  )

let synth_extra_bv8_inverse (n: nat) : Lemma (synth_inverse (synth_extra_bv8 n) (synth_extra_bv8_recip n))
  [SMTPat (synth_inverse (synth_extra_bv8 n) (synth_extra_bv8_recip n))]
=
  synth_inverse_intro' (synth_extra_bv8 n) (synth_extra_bv8_recip n) (fun x ->
    of_uint8_to_uint8 x
  )

let parse_extra_bv8_kind (n: nat) : Tot parser_kind = 
  parse_filter_kind parse_u8_kind

let parse_extra_bv8 (n: nat) : Tot (parser (parse_extra_bv8_kind n) (BV.bv_t (n % 8))) =
  (parse_u8 `parse_filter` extra_bytes_prop n) `parse_synth` synth_extra_bv8 n

let serialize_extra_bv8 (n: nat) : Tot (serializer (parse_extra_bv8 n)) =
  serialize_synth
    _
    (synth_extra_bv8 n)
    (serialize_filter serialize_u8 (extra_bytes_prop n))
    (synth_extra_bv8_recip n)
    ()

(* parse a bitvector, general *)

let synth_bv (n: nat) (x: (BV.bv_t (n % 8) & BV.bv_t (8 * (n / 8)))) : Tot (BV.bv_t n) =
  Seq.append (fst x) (snd x)

let synth_bv_recip (n: nat) (x: BV.bv_t n) : Tot (BV.bv_t (n % 8) & BV.bv_t (8 * (n / 8))) =
  Seq.slice x 0 (n % 8), Seq.slice x (n % 8) (Seq.length x)

let synth_bv_injective (n: nat) : Lemma
  (synth_injective (synth_bv n))
  [SMTPat (synth_injective (synth_bv n))]
= synth_inverse_intro' (synth_bv_recip n) (synth_bv n) (fun x ->
    let (hd, tl) = x in
    let (hd', tl') = synth_bv_recip n (synth_bv n x) in
    assert (hd `Seq.equal` hd');
    assert (tl `Seq.equal` tl')
  )

let synth_bv_inverse (n: nat) : Lemma
  (synth_inverse (synth_bv n) (synth_bv_recip n))
  [SMTPat (synth_inverse (synth_bv n) (synth_bv_recip n))]
= synth_inverse_intro' (synth_bv n) (synth_bv_recip n) (fun x ->
    assert (synth_bv n (synth_bv_recip n x) `Seq.equal` x)
  )

let parse_bv_kind (n: nat) : Tot parser_kind =
  if n % 8 = 0
  then strong_parser_kind (n / 8) (n / 8) (Some ParserKindMetadataTotal)
  else strong_parser_kind (1 + n / 8) (1 + n / 8) None

let parse_bv (n: nat) : Tot (parser (parse_bv_kind n) (BV.bv_t n)) =
  if n % 8 = 0 then parse_byte_bv (n / 8) else ((parse_extra_bv8 n `nondep_then` parse_byte_bv (n / 8)) `parse_synth` synth_bv n)

let serialize_bv (n: nat) : Tot (serializer (parse_bv n)) =
  if n % 8 = 0
  then serialize_byte_bv (n / 8)
  else
    serialize_synth
      _
      (synth_bv n)
      (serialize_extra_bv8 n `serialize_nondep_then` serialize_byte_bv (n / 8))
      (synth_bv_recip n)
      ()

(* parse a bounded bit vector *)

module U32 = FStar.UInt32

open LowParse.Spec.BoundedInt

inline_for_extraction
let bounded_bv_t
  (min: nat)
  (max: nat { min <= max })
: Tot Type
= (bitsize: bounded_int32 min max & BV.bv_t (U32.v bitsize))

let parse_bounded_bv_payload_kind
  (min: nat)
  (max: nat { min <= max })
: Tot parser_kind
= strong_parser_kind
    (if min % 8 = 0 then min / 8 else 1 + min / 8)
    (if max % 8 = 0 then max / 8 else 1 + max / 8)
    None

let parse_bounded_bv_payload_kind_is_weaker_than_parse_bv_kind
  (min: nat)
  (max: nat)
  (n: nat)
: Lemma
  (requires (min <= n /\ n <= max))
  (ensures (
    min <= n /\
    n <= max /\
    parse_bounded_bv_payload_kind min max `is_weaker_than` parse_bv_kind n
  ))
  [SMTPat (parse_bounded_bv_payload_kind min max `is_weaker_than` parse_bv_kind n)]
= ()

let parse_bounded_bv_kind
  (min: nat)
  (max: nat { min <= max })
  (hk: parser_kind)
: Tot parser_kind
= hk `and_then_kind` parse_bounded_bv_payload_kind min max

let parse_bounded_bv
  (min: nat)
  (max: nat { min <= max })
  (#hk: parser_kind)
  (hp: parser hk (bounded_int32 min max))
: Tot (parser (parse_bounded_bv_kind min max hk) (bounded_bv_t min max))
= parse_dtuple2
    hp
    (fun (sz: bounded_int32 min max) -> weaken (parse_bounded_bv_payload_kind min max) (parse_bv (U32.v sz)))

let serialize_bounded_bv
  (min: nat)
  (max: nat { min <= max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 min max))
  (hs: serializer hp { hk.parser_kind_subkind == Some ParserStrong })
: Tot (serializer (parse_bounded_bv min max hp))
= serialize_dtuple2
    hs
    (fun (sz: bounded_int32 min max) -> serialize_weaken (parse_bounded_bv_payload_kind min max) (serialize_bv (U32.v sz)))
