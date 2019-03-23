module LowParse.Low.BCVLI
include LowParse.Spec.BCVLI
include LowParse.Low.Combinators
include LowParse.Low.BoundedInt

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module Cast = FStar.Int.Cast
module U32 = FStar.UInt32

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0"

#push-options "--z3rlimit 16"

let validate_bcvli : validator parse_bcvli =
  fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts parse_bcvli h input pos;
    parse_bcvli_eq (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    valid_facts (parse_bounded_integer_le 1) h input pos
  in
  let pos1 = validate_total_constant_size (parse_bounded_integer_le 1) 1ul () input pos in
  if validator_max_length `U32.lt` pos1
  then pos1
  else
    [@inline_let] let _ =
      valid_facts (parse_bounded_integer_le 2) h input pos1;
      valid_facts (parse_bounded_integer_le 4) h input pos1
    in
    let r = read_bounded_integer_le_1 input pos in
    if r `U32.lt` 253ul
    then pos1
    else if r = 253ul
    then
      let pos2 = validate_total_constant_size (parse_bounded_integer_le 2) 2ul () input pos1 in
      if validator_max_length `U32.lt` pos2
      then pos2
      else
        (* because of the non-malleability constraint, I need to actually read the value and check whether it is not a lower integer *)
        let r = read_bounded_integer_le_2 input pos1 in
        if r `U32.lt` 253ul
        then validator_error_generic
        else pos2
    else if r = 254ul
    then
      let pos2 = validate_total_constant_size (parse_bounded_integer_le 4) 4ul () input pos1 in
      if validator_max_length `U32.lt` pos2
      then pos2
      else
        (* because of the non-malleability constraint, I need to actually read the value and check whether it is not a lower integer *)
        let r = read_bounded_integer_le_4 input pos1 in
        if r `U32.lt` 65536ul
        then validator_error_generic
        else pos2
    else validator_error_generic

let jump_bcvli : jumper parse_bcvli =
  fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts parse_bcvli h input pos;
    parse_bcvli_eq (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    valid_facts (parse_bounded_integer_le 1) h input pos
  in
  let pos1 = jump_constant_size (parse_bounded_integer_le 1) 1ul () input pos in
  [@inline_let] let _ =
    valid_facts (parse_bounded_integer_le 2) h input pos1;
    valid_facts (parse_bounded_integer_le 4) h input pos1
  in
  let r = read_bounded_integer_le_1 input pos in
  if r `U32.lt` 253ul
  then pos1
  else if r = 253ul
  then
    jump_constant_size (parse_bounded_integer_le 2) 2ul () input pos1
  else
    jump_constant_size (parse_bounded_integer_le 4) 4ul () input pos1

let read_bcvli : leaf_reader parse_bcvli =
  fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts parse_bcvli h input pos;
    parse_bcvli_eq (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    valid_facts (parse_bounded_integer_le 1) h input pos
  in
  let r = read_bounded_integer_le_1 input pos in
  if r `U32.lt` 253ul
  then (r <: U32.t)
  else
    let pos1 = jump_constant_size (parse_bounded_integer_le 1) 1ul () input pos in
    [@inline_let] let _ =
      valid_facts (parse_bounded_integer_le 2) h input pos1;
      valid_facts (parse_bounded_integer_le 4) h input pos1
    in
    if r = 253ul
    then read_bounded_integer_le_2 input pos1 <: U32.t
    else read_bounded_integer_le_4 input pos1 <: U32.t

#pop-options

module U8 = FStar.UInt8

#push-options "--z3rlimit 16"

inline_for_extraction
let serialize32_bcvli'
  (x: U32.t)
  (b: buffer8)
: HST.Stack U32.t
  (requires (fun h -> B.live h b /\ Seq.length (serialize serialize_bcvli x) <= B.length b))
  (ensures (fun h len h' ->
    Seq.length (serialize serialize_bcvli x) == U32.v len /\ (
    let b' = B.gsub b 0ul len in
    B.modifies (B.loc_buffer b') h h' /\
    B.live h b /\
    B.as_seq h' b' `Seq.equal` serialize serialize_bcvli x
  )))
= [@inline_let] let _ = serialize_bcvli_eq x in
  let c : bounded_integer 1 =
    if x `U32.lt` 253ul
    then x
    else if x `U32.lt` 65536ul
    then 253ul
    else 254ul
  in
  let len1 = serialize32_bounded_integer_le_1 c b in
  if c `U32.lt` 253ul
  then len1
  else if c = 253ul
  then
    let _ = assert (U32.v x < 65536) in
    let len2 = serialize32_bounded_integer_le_2 x (B.offset b len1) in
    len1 `U32.add` len2
  else begin
    let len2 = serialize32_bounded_integer_le_4 x (B.offset b len1) in
    len1 `U32.add` len2
  end

#pop-options

inline_for_extraction
let serialize32_bcvli : serializer32 serialize_bcvli =
  fun (x: U32.t) (b: buffer8) -> serialize32_bcvli' x b

let write_bcvli : leaf_writer_strong serialize_bcvli =
  leaf_writer_strong_of_serializer32 serialize32_bcvli ()
