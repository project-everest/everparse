module LowParse.Low.ErrorCode

(*

Error codes for validators

TODO: replace with type classes

inline_for_extraction
let default_validator_cls : validator_cls = {
  validator_max_length = 4294967279ul;
}

*)

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

[@ CMacro ]
let max_uint32 : U32.t = 4294967295ul

let max_uint32_correct
  (x: U32.t)
: Lemma
  (U32.v x <= U32.v max_uint32)
= ()

inline_for_extraction
noextract
let _max_uint32_as_uint64 : U64.t = 4294967295uL


[@ CMacro ]
let max_uint32_as_uint64 : U64.t = _max_uint32_as_uint64

[@ CMacro ]
let validator_max_length : (u: U64.t { 4 <= U64.v u /\ U64.v u <= U64.v max_uint32_as_uint64 } ) = _max_uint32_as_uint64

[@ CInline ]
let is_error (positionOrError: U64.t) : Tot bool = positionOrError `U64.gt` validator_max_length

[@ CInline ]
let is_success (positionOrError: U64.t) : Tot bool = positionOrError `U64.lte` validator_max_length

[@ CMacro ]
type validator_error = (u: U64.t { is_error u } )

inline_for_extraction
let pos_t = (pos: U64.t {is_success pos})

module BF = LowParse.BitFields

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let get_validator_error_field (x: U64.t) (lo: nat) (hi: nat { lo < hi /\ hi <= 32 }) : Tot (code: U64.t { 0 <= U64.v code /\ U64.v code < pow2 (hi - lo) }) =
  [@inline_let]
  let res =
    BF.uint64.BF.get_bitfield x (32 + lo) (32 + hi)
  in
  res

inline_for_extraction
noextract
let set_validator_error_field (x: U64.t) (lo: nat) (hi: nat { lo < hi /\ hi <= 32 }) (code: U64.t { 0 < U64.v code /\ U64.v code < pow2 (hi - lo) }) : Tot validator_error =
  [@inline_let]
  let res =
    BF.uint64.BF.set_bitfield x (32 + lo) (32 + hi) code
  in
  [@inline_let]
  let _ =
    BF.get_bitfield_set_bitfield_same #64 (U64.v x) (32 + lo) (32 + hi) (U64.v code);
    BF.get_bitfield_zero_inner (U64.v res) 32 64 (32 + lo) (32 + hi);
    assert (BF.get_bitfield (U64.v res) 32 64 > 0);
    Classical.move_requires (BF.lt_pow2_get_bitfield_hi (U64.v res)) 32;
    assert_norm (pow2 32 == U64.v validator_max_length + 1)
  in
  res

let get_validator_error_field_set_validator_error_field
  (x: U64.t)
  (lo: nat)
  (hi: nat { lo < hi /\ hi <= 32 })
  (code: U64.t { 0 < U64.v code /\ U64.v code < pow2 (hi - lo) })
: Lemma
  (get_validator_error_field (set_validator_error_field x lo hi code) lo hi == code)
= ()

[@ CInline ]
let set_validator_error_pos (error: validator_error) (position: pos_t) : Tot validator_error =
  [@inline_let]
  let res =
    BF.uint64.BF.set_bitfield error 0 32 position
  in
  [@inline_let]
  let _ =
    BF.get_bitfield_set_bitfield_other (U64.v error) 0 32 (U64.v position) 32 64;
    assert (BF.get_bitfield (U64.v res) 32 64 == BF.get_bitfield (U64.v error) 32 64);
    Classical.move_requires (BF.get_bitfield_hi_lt_pow2 (U64.v error)) 32;
    Classical.move_requires (BF.lt_pow2_get_bitfield_hi (U64.v res)) 32;
    assert_norm (pow2 32 == U64.v validator_max_length + 1)
  in
  res

#pop-options

[@ CInline ]
let get_validator_error_pos (x: U64.t) : Tot pos_t =
  (BF.uint64.BF.get_bitfield x 0 32)

[@ CInline ]
let set_validator_error_kind (error: U64.t) (code: U64.t { 0 < U64.v code /\ U64.v code < 16384 }) : Tot validator_error =
  set_validator_error_field error 0 14 code

[@ CInline ]
let get_validator_error_kind (error: U64.t) : Tot (code: U64.t { 0 <= U64.v code /\ U64.v code < 16384 }) =
  get_validator_error_field error 0 14

inline_for_extraction
let error_code = (c: U64.t { 0 < U64.v c /\ U64.v c < 65536 })

[@ CInline ]
let set_validator_error_code (error: U64.t) (code: error_code) : Tot validator_error =
  set_validator_error_field error 16 32 code

[@ CInline ]
let get_validator_error_code (error: U64.t) : Tot (code: U64.t { U64.v code < 65536 }) =
  get_validator_error_field error 16 32

[@ CMacro ]
let validator_error_generic : validator_error = normalize_term (set_validator_error_kind 0uL 1uL)

[@ CMacro ]
let validator_error_not_enough_data : validator_error = normalize_term (set_validator_error_kind 0uL 2uL)

[@"opaque_to_smt"] // to hide the modulo operation
inline_for_extraction
noextract
let uint64_to_uint32
  (x: pos_t)
: Tot (y: U32.t { U32.v y == U64.v x })
= Cast.uint64_to_uint32 x

// [@ CInline ]
// let maybe_set_error_code (res:U64.t)  (pos:pos_t) (c:U64.t { 0 < U64.v c /\ U64.v c < 65536 })
//   : Tot U64.t
//   = if is_error res && get_validator_error_code res = 0uL
//     then set_validator_error_pos (set_validator_error_code res c) pos
//     else res

[@ CInline ]
let set_validator_error_pos_and_code
  (error: validator_error)
  (position: pos_t)
  (code: error_code)
: Tot validator_error
= set_validator_error_pos (set_validator_error_code error code) position

[@ CInline ]
let maybe_set_validator_error_pos_and_code
  (error: validator_error)
  (pos: pos_t)
  (c: error_code)
: Tot validator_error
= if get_validator_error_code error = 0uL
  then set_validator_error_pos_and_code error pos c
  else error

[@ CInline ]
let maybe_set_error_code
  (positionOrError: U64.t)
  (positionAtError: pos_t)
  (code: error_code)
 : Tot U64.t
  = if is_error positionOrError
    && get_validator_error_code positionOrError = 0uL
    then set_validator_error_pos_and_code positionOrError positionAtError code
    else positionOrError
