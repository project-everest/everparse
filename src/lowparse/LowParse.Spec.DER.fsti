module LowParse.Spec.DER
include LowParse.Spec.Int
include LowParse.Spec.BoundedInt

open FStar.Mul

module U8 = FStar.UInt8
module UInt = FStar.UInt
module Seq = FStar.Seq
module Math = LowParse.Math
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

let der_length_max : nat = 2743062034396844341627968125593604635037196317966166035056000994228098690879836473582587849768181396806642362668936055872479091931372323951612051859122835149807249350355003132267795098895967012320756270631179897595796976964454084495146379250195728106130226298287754794921070036903071843030324651025760255

// _ by (FStar.Tactics.(exact (norm_term [delta; iota; zeta; primops] (`(pow2 (8 * 126) - 1)))))

val der_length_max_eq : squash (der_length_max == pow2 (8 * 126) - 1)

// let _ = intro_ambient der_length_max

let der_length_t = (x: nat { x <= der_length_max })

noextract
val log256
  (x: nat { x > 0 })
: Tot (y: nat { y > 0 /\ pow2 (8 * (y - 1)) <= x /\ x < pow2 (8 * y)})

val log256_unique
  (x: nat)
  (y: nat)
: Lemma
  (requires (
    x > 0 /\
    y > 0 /\
    pow2 (8 * (y - 1)) <= x /\
    x < pow2 (8 * y)
  ))
  (ensures (y == log256 x))

val log256_le
  (x1 x2: nat)
: Lemma
  (requires (0 < x1 /\ x1 <= x2))
  (ensures (log256 x1 <= log256 x2))

inline_for_extraction // for parser_kind
let der_length_payload_size_of_tag
  (x: U8.t)
: Tot (y: nat { y <= 126 })
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  [@inline_let]
  let x' = U8.v x in
  if x' <= 128 || x' = 255
  then
    0
  else
    x' - 128

inline_for_extraction
let parse_der_length_payload_kind (x: U8.t) : Tot parser_kind =
  let len = der_length_payload_size_of_tag x in
  strong_parser_kind len len None

noextract
let tag_of_der_length
  (x: der_length_t)
: Tot U8.t
= if x < 128
  then U8.uint_to_t x
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126);
    128uy `U8.add` U8.uint_to_t len_len

noextract
let der_length_payload_size
  (x: der_length_t)
: Tot (y: nat { y <= 126 })
= der_length_payload_size_of_tag (tag_of_der_length x)

val der_length_payload_size_le
  (x1 x2: der_length_t)
: Lemma
  (requires (x1 <= x2))
  (ensures (der_length_payload_size x1 <= der_length_payload_size x2))

let lint (len: nat) : Tot Type = (x: nat { x < pow2 (8 * len) })

module U32 = FStar.UInt32

let tag_of_der_length32
  (x: U32.t)
: GTot U8.t
= let _ = assert_norm (pow2 32 - 1 <= der_length_max) in
  tag_of_der_length (U32.v x)

val parse_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (parser (parse_der_length_payload_kind x) (refine_with_tag tag_of_der_length32 x))

val parse_der_length_payload32_unfold
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
  (input: bytes)
: Lemma
  (
    let y = parse (parse_der_length_payload32 x) input in
    (256 < der_length_max) /\ (
    if U8.v x < 128
    then tag_of_der_length (U8.v x) == x /\ y == Some (Cast.uint8_to_uint32 x, 0)
    else if x = 128uy || x = 255uy
    then y == None
    else if x = 129uy
    then
      match parse parse_u8 input with
      | None -> y == None
      | Some (z, consumed) ->
        if U8.v z < 128
        then y == None
        else tag_of_der_length (U8.v z) == x /\ y == Some (Cast.uint8_to_uint32 z, consumed)
    else
      let len : nat = U8.v x - 128 in
      2 <= len /\ len <= 4 /\
      (
      let res : option (bounded_integer len & consumed_length input) = parse (parse_bounded_integer len) input in
      match res with
      | None -> y == None
      | Some (z, consumed) ->
        len > 0 /\ (
        if U32.v z >= pow2 (8 * (len - 1))
        then U32.v z <= der_length_max /\ tag_of_der_length32 z == x /\ y == Some ((z <: refine_with_tag tag_of_der_length32 x), consumed)
        else y == None
  ))))

val log256_eq
  (x: nat)
: Lemma
  (requires (x > 0 /\ x < 4294967296))
  (ensures (log256 x == log256' x))

inline_for_extraction
let tag_of_der_length32'
  (x: der_length_t { x < 4294967296 } )
: Tot (z: U8.t { z == tag_of_der_length x })
= if x < 128
  then U8.uint_to_t x
  else
    [@inline_let]
    let len_len = log256' x in
    [@inline_let] let _ =
      log256_eq x;
      assert_norm (der_length_max == pow2 (8 * 126) - 1);
      Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)
    in
    128uy `U8.add` U8.uint_to_t len_len

inline_for_extraction
let parse_bounded_der_length_payload32_kind
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 } )
: Tot parser_kind
= [@inline_let] let _ = der_length_payload_size_le min max in
  strong_parser_kind (der_length_payload_size_of_tag (tag_of_der_length32' min)) (der_length_payload_size_of_tag (tag_of_der_length32' max)) None

inline_for_extraction
let parse_bounded_der_length32_kind
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 } )
: Tot parser_kind
= 
[@inline_let]
let k = parse_bounded_der_length_payload32_kind min max in
strong_parser_kind (1 + der_length_payload_size_of_tag (tag_of_der_length32' min)) (1 + der_length_payload_size_of_tag (tag_of_der_length32' max)) None

val parse_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
: Tot (parser (parse_bounded_der_length32_kind min max) (bounded_int32 min max))

val parse_bounded_der_length32_unfold
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
  (input: bytes)
: Lemma
  (let res = parse (parse_bounded_der_length32 min max) input in
   match parse parse_u8 input with
   | None -> res == None
   | Some (x, consumed_x) ->
     let len = der_length_payload_size_of_tag x in
     if der_length_payload_size min <= len && len <= der_length_payload_size max then
      let input' = Seq.slice input consumed_x (Seq.length input) in
      len <= 4 /\ (
      match parse (parse_der_length_payload32 x) input' with
      | Some (y, consumed_y) ->
        if min <= U32.v y && U32.v y <= max
        then res == Some (y, consumed_x + consumed_y)
        else res == None
      | None -> res == None
     ) else
       res == None
 )

inline_for_extraction
let der_length_payload_size_of_tag8
  (x: U8.t)
: Tot (y: U8.t { U8.v y == der_length_payload_size_of_tag x } )
= [@inline_let]
  let _ =
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    assert_norm (pow2 7 == 128);
    assert_norm (pow2 8 == 256);
    assert_norm (256 < der_length_max);
    assert (U8.v x <= der_length_max)
  in
  if x `U8.lt` 129uy || x = 255uy
  then
    0uy
  else
    x `U8.sub` 128uy

inline_for_extraction
let log256_32
  (n: U32.t { U32.v n > 0 } )
: Tot (y: U8.t { U8.v y == log256' (U32.v n) } )
= if n `U32.lt` 256ul
  then 1uy
  else if n `U32.lt` 65536ul
  then 2uy
  else if n `U32.lt` 16777216ul
  then 3uy
  else 4uy

inline_for_extraction
let tag_of_der_length32_impl
  (x: U32.t)
: Tot (y: U8.t { U32.v x < der_length_max /\ y == tag_of_der_length (U32.v x) } )
= [@inline_let]
  let _ = assert_norm (4294967296 <= der_length_max) in
  if x `U32.lt` 128ul
  then begin
    [@inline_let] let _ = FStar.Math.Lemmas.small_modulo_lemma_1 (U32.v x) 256 in
    Cast.uint32_to_uint8 x <: U8.t
  end else
    let len_len = log256_32 x in
    [@inline_let] let _ =
      log256_eq (U32.v x);
      assert_norm (der_length_max == pow2 (8 * 126) - 1);
      Math.pow2_lt_recip (8 * (U8.v len_len - 1)) (8 * 126)
    in
    128uy `U8.add` len_len

val serialize_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
: Tot (serializer (parse_bounded_der_length32 min max))

val serialize_bounded_der_length32_unfold
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
  (y': bounded_int32 min max)
: Lemma
  (
    let res = serialize (serialize_bounded_der_length32 min max) y' in
    let x = tag_of_der_length32_impl y' in
    let s1 = Seq.create 1 x in
    if x `U8.lt` 128uy
    then res `Seq.equal` s1
    else if x = 129uy
    then U32.v y' <= 255 /\ res `Seq.equal` (s1 `Seq.append` Seq.create 1 (Cast.uint32_to_uint8 y'))
    else
      let len = log256' (U32.v y') in
      res `Seq.equal` (s1 `Seq.append` serialize (serialize_bounded_integer len) y')
  )

val serialize_bounded_der_length32_size
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
  (y': bounded_int32 min max)
: Lemma
  (
    Seq.length (serialize (serialize_bounded_der_length32 min max) y') == (
      if y' `U32.lt` 128ul
      then 1
      else if y' `U32.lt` 256ul
      then 2
      else if y' `U32.lt` 65536ul
      then 3
      else if y' `U32.lt` 16777216ul
      then 4
      else 5
 ))
