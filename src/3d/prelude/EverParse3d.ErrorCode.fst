module EverParse3d.ErrorCode

module U64 = FStar.UInt64
module BF = LowParse.BitFields

inline_for_extraction
noextract
let error_width = 4

inline_for_extraction
noextract
let pos_width = normalize_term (64 - error_width)

[@ CMacro ]
let validator_max_length : (u: U64.t { 4 <= U64.v u /\ U64.v u == pow2 pos_width - 1 } ) =
  FStar.Math.Lemmas.pow2_le_compat 64 pos_width;
  [@inline_let]
  let x =  U64.uint_to_t (pow2 pos_width - 1) in
  normalize_term_spec x;
  normalize_term x

[@ CInline ]
let is_error (positionOrError: U64.t) : Tot bool = positionOrError `U64.gt` validator_max_length

[@ CInline ]
let is_success (positionOrError: U64.t) : Tot bool = positionOrError `U64.lte` validator_max_length

inline_for_extraction
noextract
type validator_error = (u: U64.t { is_error u } )

inline_for_extraction
noextract
let pos_t = (pos: U64.t {is_success pos})

module BF = LowParse.BitFields

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let get_validator_error_field (x: U64.t) (lo: nat) (hi: nat { lo < hi /\ hi <= error_width }) : Tot (code: U64.t { 0 <= U64.v code /\ U64.v code < pow2 (hi - lo) }) =
  [@inline_let]
  let res =
    BF.uint64.BF.get_bitfield x (pos_width + lo) (pos_width + hi)
  in
  res

inline_for_extraction
noextract
let set_validator_error_field (x: U64.t) (lo: nat) (hi: nat { lo < hi /\ hi <= error_width }) (code: U64.t { 0 < U64.v code /\ U64.v code < pow2 (hi - lo) }) : Tot validator_error =
  [@inline_let]
  let res =
    BF.uint64.BF.set_bitfield x (pos_width + lo) (pos_width + hi) code
  in
  [@inline_let]
  let _ =
    BF.get_bitfield_set_bitfield_same #64 (U64.v x) (pos_width + lo) (pos_width + hi) (U64.v code);
    BF.get_bitfield_zero_inner (U64.v res) pos_width 64 (pos_width + lo) (pos_width + hi);
    assert (BF.get_bitfield (U64.v res) pos_width 64 > 0);
    Classical.move_requires (BF.lt_pow2_get_bitfield_hi (U64.v res)) pos_width;
    assert_norm (pow2 pos_width == U64.v validator_max_length + 1)
  in
  res

let get_validator_error_field_set_validator_error_field
  (x: U64.t)
  (lo: nat)
  (hi: nat { lo < hi /\ hi <= error_width })
  (code: U64.t { 0 < U64.v code /\ U64.v code < pow2 (hi - lo) })
: Lemma
  (get_validator_error_field (set_validator_error_field x lo hi code) lo hi == code)
= ()

[@ CInline ]
let set_validator_error_pos (error: validator_error) (position: pos_t) : Tot validator_error =
  [@inline_let]
  let res =
    BF.uint64.BF.set_bitfield error 0 pos_width position
  in
  [@inline_let]
  let _ =
    BF.get_bitfield_set_bitfield_other (U64.v error) 0 pos_width (U64.v position) pos_width 64;
    assert (BF.get_bitfield (U64.v res) pos_width 64 == BF.get_bitfield (U64.v error) pos_width 64);
    Classical.move_requires (BF.get_bitfield_hi_lt_pow2 (U64.v error)) pos_width;
    Classical.move_requires (BF.lt_pow2_get_bitfield_hi (U64.v res)) pos_width;
    assert_norm (pow2 pos_width == U64.v validator_max_length + 1)
  in
  res

#pop-options

[@ CInline ]
let get_validator_error_pos (x: U64.t) : Tot pos_t =
  (BF.uint64.BF.get_bitfield x 0 pos_width)

[@ CInline ]
let set_validator_error_kind (error: U64.t) (code: U64.t { 0 < U64.v code /\ U64.v code < normalize_term (pow2 error_width) }) : Tot validator_error =
  normalize_term_spec (pow2 error_width);
  set_validator_error_field error 0 error_width code

[@ CInline ]
let get_validator_error_kind (error: U64.t) : Tot (code: U64.t { 0 <= U64.v code /\ U64.v code < normalize_term (pow2 error_width) }) =
  normalize_term_spec (pow2 error_width);
  get_validator_error_field error 0 error_width

let get_validator_error_kind_set_validator_error_kind (error: U64.t) (code: U64.t {0 < U64.v code /\ U64.v code < normalize_term (pow2 error_width)}) : Lemma
  (get_validator_error_kind (set_validator_error_kind error code) == code)
  [SMTPat (get_validator_error_kind (set_validator_error_kind error code))]
= assert_norm (normalize_term (pow2 error_width) == pow2 error_width);
  get_validator_error_field_set_validator_error_field error 0 error_width code

[@ CMacro ]
let validator_error_generic : validator_error = normalize_term (set_validator_error_kind 0uL 1uL)

[@ CMacro ]
let validator_error_not_enough_data : validator_error = normalize_term (set_validator_error_kind 0uL 2uL)

[@ CMacro ]
let validator_error_impossible : validator_error = normalize_term (set_validator_error_kind 0uL 3uL)

[@ CMacro ]
let validator_error_list_size_not_multiple : validator_error = normalize_term (set_validator_error_kind 0uL 4uL)

[@ CMacro ]
let validator_error_action_failed : validator_error = normalize_term (set_validator_error_kind 0uL 5uL)

[@ CMacro ]
let validator_error_constraint_failed : validator_error = normalize_term (set_validator_error_kind 0uL 6uL)

[@ CMacro ]
let validator_error_unexpected_padding : validator_error = normalize_term (set_validator_error_kind 0uL 7uL)

let error_reason_of_result (code:U64.t) : string =
  match (get_validator_error_kind code) with
  | 1uL -> "generic error"
  | 2uL -> "not enough data"
  | 3uL -> "impossible"
  | 4uL -> "list size not multiple of element size"
  | 5uL -> "action failed"
  | 6uL -> "constraint failed"
  | 7uL -> "unexpected padding"
  | _ -> "unspecified"

[@ CInline ]
let check_constraint_ok (ok:bool) (position: pos_t): Tot U64.t =
      if ok
      then position
      else set_validator_error_pos validator_error_constraint_failed position

////////////////////////////////////////////////////////////////////////////////
// Some generic helpers
////////////////////////////////////////////////////////////////////////////////

module U32 = FStar.UInt32

[@ CInline ]
let is_range_okay (size offset access_size:U32.t)
  : bool
  = let open U32 in
    size >=^ access_size &&
    size -^ access_size >=^ offset

(* Context for default error handler *)

noeq
type error_frame = {
  filled: bool;
  start_pos: U64.t;
  typename_s: string;
  fieldname: string;
  reason: string;
}
