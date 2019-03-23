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
  fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts parse_bcvli h input pos;
    parse_bcvli_eq (bytes_of_slice_from h input pos);
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
  fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts parse_bcvli h input pos;
    parse_bcvli_eq (bytes_of_slice_from h input pos);
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
  fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts parse_bcvli h input pos;
    parse_bcvli_eq (bytes_of_slice_from h input pos);
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

#push-options "--z3rlimit 32"

inline_for_extraction
let serialize32_bcvli'
  (x: U32.t)
  (#rrel #rel: _)
  (b: B.mbuffer U8.t rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let len = Seq.length (serialize serialize_bcvli x) in
    B.live h b /\
    U32.v pos + len <= B.length b /\
    writable b (U32.v pos) (U32.v pos + len) h
  ))
  (ensures (fun h len h' ->
    Seq.length (serialize serialize_bcvli x) == U32.v len /\ (
    B.modifies (B.loc_buffer_from_to b pos (pos `U32.add` len)) h h' /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + U32.v len) `Seq.equal` serialize serialize_bcvli x
  )))
= // [@inline_let] let _ = 
    serialize_bcvli_eq x
;  // in
  let c : bounded_integer 1 =
    if x `U32.lt` 253ul
    then x
    else if x `U32.lt` 65536ul
    then 253ul
    else 254ul
  in
  [@inline_let]
  let pos' = Ghost.hide (U32.v pos + Seq.length (serialize serialize_bcvli x)) in
  let h = HST.get () in
  [@inline_let]
  let _ = writable_weaken b (U32.v pos) (Ghost.reveal pos') h (U32.v pos) (U32.v pos + 1) in
  let len1 = serialize32_bounded_integer_le_1 c b pos in
  let h1 = HST.get () in
  [@inline_let]
  let _ = writable_modifies b (U32.v pos) (Ghost.reveal pos') h B.loc_none h1 in
  if c `U32.lt` 253ul
  then begin
    len1
  end else if c = 253ul
  then begin
    [@inline_let]
    let _ = assert (U32.v x < 65536) in
    [@inline_let]
    let _ = writable_weaken b (U32.v pos) (Ghost.reveal pos') h1 (U32.v pos + U32.v len1) ((U32.v pos + U32.v len1) + 2) in
    let len2 = serialize32_bounded_integer_le_2 x b (pos `U32.add` len1) in
    let h'  = HST.get () in
    [@inline_let]
    let len = len1 `U32.add` len2 in
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` len1) (B.loc_buffer_from_to b (pos `U32.add` len1) (pos `U32.add` len)) h1 h';    
    len
  end else begin
    [@inline_let]
    let _ = writable_weaken b (U32.v pos) (Ghost.reveal pos') h1 (U32.v pos + U32.v len1) ((U32.v pos + U32.v len1) + 4) in
    let len2 = serialize32_bounded_integer_le_4 x b (pos `U32.add` len1) in
    let h' = HST.get () in
    [@inline_let]
    let len = len1 `U32.add` len2 in
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` len1) (B.loc_buffer_from_to b (pos `U32.add` len1) (pos `U32.add` len)) h1 h';
    len
  end

#pop-options

inline_for_extraction
let serialize32_bcvli : serializer32 serialize_bcvli =
  fun (x: U32.t) #rrel #rel b pos -> serialize32_bcvli' x b pos

let write_bcvli : leaf_writer_strong serialize_bcvli =
  leaf_writer_strong_of_serializer32 serialize32_bcvli ()
