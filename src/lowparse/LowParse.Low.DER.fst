module LowParse.Low.DER
include LowParse.Spec.DER
include LowParse.Low.Int // for parse_u8
include LowParse.Low.BoundedInt // for bounded_integer
open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

#push-options "--z3rlimit 32"

inline_for_extraction
let validate_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (validator (parse_der_length_payload32 x))
= fun #rrel #rel input pos ->
    let h = HST.get () in
    [@inline_let] let _ =
      valid_facts (parse_der_length_payload32 x) h input (uint64_to_uint32 pos);
      assert (U64.v pos <= U32.v input.len);
      parse_der_length_payload32_unfold x (bytes_of_slice_from h input (uint64_to_uint32 pos));
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then pos
    else if x = 128uy || x = 255uy
    then validator_error_generic
    else if x = 129uy
    then
      [@inline_let] let _ = valid_facts parse_u8 h input (uint64_to_uint32 pos) in
      let v = validate_u8 () input pos in
      if is_error v
      then v
      else
        let z = read_u8 input (uint64_to_uint32 pos) in
        if z `U8.lt` 128uy
        then validator_error_generic
        else v
    else
      let len = x `U8.sub` 128uy in
      [@inline_let] let _ = valid_facts (parse_bounded_integer (U8.v len)) h input (uint64_to_uint32 pos) in
      if len = 2uy
      then
        let v = validate_bounded_integer 2 input pos in
        if is_error v
        then v
        else
          let y = read_bounded_integer_2 () input (uint64_to_uint32 pos) in
          if y `U32.lt `256ul
          then validator_error_generic
          else v
      else if len = 3uy
      then
        let v = validate_bounded_integer 3 input pos in
        if is_error v
        then v
        else
          let y = read_bounded_integer_3 () input (uint64_to_uint32 pos) in
          if y `U32.lt `65536ul
          then validator_error_generic
          else v
      else
        let v = validate_bounded_integer 4 input pos in
        if is_error v
        then v
        else
          let y = read_bounded_integer_4 () input (uint64_to_uint32 pos) in
          if y `U32.lt` 16777216ul
          then validator_error_generic
          else v

inline_for_extraction
let jump_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (jumper (parse_der_length_payload32 x))
= fun #rrel #rel input pos ->
    let h = HST.get () in
    [@inline_let] let _ =
      valid_facts (parse_der_length_payload32 x) h input pos;
      parse_der_length_payload32_unfold x (bytes_of_slice_from h input pos);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then pos
    else
      [@inline_let]
      let len = x `U8.sub` 128uy in
      [@inline_let] let _ =
        valid_facts parse_u8 h input pos;
        parser_kind_prop_equiv parse_u8_kind parse_u8;
        valid_facts (parse_bounded_integer (U8.v len)) h input pos;
        parser_kind_prop_equiv (parse_bounded_integer_kind (U8.v len)) (parse_bounded_integer (U8.v len))
      in
      pos `U32.add` Cast.uint8_to_uint32 len

inline_for_extraction
let read_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (leaf_reader (parse_der_length_payload32 x))
= fun #rrel #rel input pos ->
    let h = HST.get () in
    [@inline_let] let _ =
      valid_facts (parse_der_length_payload32 x) h input pos;
      parse_der_length_payload32_unfold x (bytes_of_slice_from h input pos);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then
      [@inline_let]
      let res = Cast.uint8_to_uint32 x in
      [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
      (res <: refine_with_tag tag_of_der_length32 x)
    else if x = 129uy
    then
      [@inline_let] let _ = valid_facts parse_u8 h input pos in
      let z = read_u8 input pos in
      [@inline_let] let res = Cast.uint8_to_uint32 z in
      [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
      (res <: refine_with_tag tag_of_der_length32 x)
    else
      let len = x `U8.sub` 128uy in
      [@inline_let] let _ = valid_facts (parse_bounded_integer (U8.v len)) h input pos in
      if len = 2uy
      then
        let res = read_bounded_integer_2 () input pos in
        [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
        (res <: refine_with_tag tag_of_der_length32 x)
      else if len = 3uy
      then
        let res = read_bounded_integer_3 () input pos in
        [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
        (res <: refine_with_tag tag_of_der_length32 x)
      else
        let res = read_bounded_integer_4 () input pos in
        [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
        (res <: refine_with_tag tag_of_der_length32 x)

inline_for_extraction
let validate_bounded_der_length32
  (vmin: der_length_t)
  (min: U32.t { U32.v min == vmin } )
  (vmax: der_length_t)
  (max: U32.t { U32.v max == vmax /\ U32.v min <= U32.v max } )
: Tot (
  validator (parse_bounded_der_length32 (vmin) (vmax)))
= fun #rrel #rel input pos ->
    let h = HST.get () in
    [@inline_let]
    let _ =
      valid_facts (parse_bounded_der_length32 (U32.v min) (U32.v max)) h input (uint64_to_uint32 pos);
      parse_bounded_der_length32_unfold (U32.v min) (U32.v max) (bytes_of_slice_from h input (uint64_to_uint32 pos));
      valid_facts parse_u8 h input (uint64_to_uint32 pos)
    in
    let v = validate_u8 () input pos in
    if is_error v
    then v
    else
      let x = read_u8 input (uint64_to_uint32 pos) in
      let len = der_length_payload_size_of_tag8 x in
      let tg1 = tag_of_der_length32_impl min in
      let l1 = der_length_payload_size_of_tag8 tg1 in
      let tg2 = tag_of_der_length32_impl max in
      let l2 = der_length_payload_size_of_tag8 tg2 in
      if (len `U8.lt` l1) || ( l2 `U8.lt` len)
      then validator_error_generic
      else
        [@inline_let] let _ = valid_facts (parse_der_length_payload32 x) h input (uint64_to_uint32 v) in
        let v2 = validate_der_length_payload32 x input v in
        if is_error v2
        then v2
        else
          let y = read_der_length_payload32 x input (uint64_to_uint32 v) in
          if y `U32.lt` min || max `U32.lt` y
          then validator_error_generic
          else v2

inline_for_extraction
let jump_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
: Tot (
  jumper (parse_bounded_der_length32 (vmin) (vmax)))
= fun #rrel #rel input pos ->
    let h = HST.get () in
    [@inline_let]
    let _ =
      valid_facts (parse_bounded_der_length32 (vmin) (vmax)) h input pos;
      parse_bounded_der_length32_unfold (vmin) (vmax) (bytes_of_slice_from h input pos);
      valid_facts parse_u8 h input pos
    in
    let v = jump_u8 input pos in
    let x = read_u8 input pos in
    let len = der_length_payload_size_of_tag8 x in
    [@inline_let] let _ = valid_facts (parse_der_length_payload32 x) h input v in
    jump_der_length_payload32 x input v

inline_for_extraction
let read_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
: Tot (
  leaf_reader (parse_bounded_der_length32 (vmin) (vmax)))
= fun #rrel #rel input pos ->
    let h = HST.get () in
    [@inline_let]
    let _ =
      valid_facts (parse_bounded_der_length32 (vmin) (vmax)) h input pos;
      parse_bounded_der_length32_unfold (vmin) (vmax) (bytes_of_slice_from h input pos);
      valid_facts parse_u8 h input pos
    in
    let v = jump_u8 input pos in
    let x = read_u8 input pos in
    let len = der_length_payload_size_of_tag8 x in
    [@inline_let] let _ = valid_facts (parse_der_length_payload32 x) h input v in
    let y = read_der_length_payload32 x input v in
    (y <: bounded_int32 (vmin) (vmax))

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
let serialize32_bounded_der_length32'
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 } )
  (y' : bounded_int32 (min) (max))
  (#rrel #rel: _)
  (b: B.mbuffer U8.t rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let len = Seq.length (serialize (serialize_bounded_der_length32 ( min) (max)) y') in
    B.live h b /\
    U32.v pos + len <= B.length b /\
    writable b (U32.v pos) (U32.v pos + len) h
  ))
  (ensures (fun h len h' ->
    let sx = serialize (serialize_bounded_der_length32 (min) (max)) y' in
    Seq.length sx == U32.v len /\ (
    B.modifies (B.loc_buffer_from_to b pos (pos `U32.add` len)) h h' /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + U32.v len) `Seq.equal` sx
  )))
= [@inline_let]
  let gpos = Ghost.hide (U32.v pos) in
  [@inline_let]
  let gpos' = Ghost.hide (U32.v pos + Seq.length (serialize (serialize_bounded_der_length32 min max) y')) in
  [@inline_let]
  let _ =
    serialize_bounded_der_length32_unfold (min) (max) y'
  in
  let x = tag_of_der_length32_impl y' in
  if x `U8.lt` 128uy
  then begin
    mbuffer_upd b gpos gpos' pos x;
    1ul
  end else
  if x = 129uy
  then begin
    mbuffer_upd b gpos gpos' pos x;
    mbuffer_upd b gpos gpos' (pos `U32.add`  1ul) (Cast.uint32_to_uint8 y');
    2ul
  end else
  if x = 130uy
  then begin
    mbuffer_upd b gpos gpos' pos x;
    let h = HST.get () in
    writable_weaken  b (Ghost.reveal gpos) (Ghost.reveal gpos') h (U32.v pos + 1) (U32.v pos + 3);
    let z = serialize32_bounded_integer_2 () y' b (pos `U32.add` 1ul) in
    let h' = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + 3)) 1;
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` 1ul) (B.loc_buffer_from_to b (pos `U32.add` 1ul) (pos `U32.add` 3ul)) h h' ;
    3ul // 1ul `U32.add` z
  end else
  if x = 131uy
  then begin
    mbuffer_upd b gpos gpos' pos x;
    let h = HST.get () in
    writable_weaken b (Ghost.reveal gpos) (Ghost.reveal gpos') h (U32.v pos + 1) (U32.v pos + 4);
    let z = serialize32_bounded_integer_3 () y' b (pos `U32.add` 1ul) in
    let h' = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + 4)) 1;
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` 1ul) (B.loc_buffer_from_to b (pos `U32.add` 1ul) (pos `U32.add` 4ul)) h h' ;
    4ul // 1ul `U32.add` z
  end else begin
    mbuffer_upd b gpos gpos' pos x;
    let h = HST.get () in
    writable_weaken b (Ghost.reveal gpos) (Ghost.reveal gpos') h (U32.v pos + 1) (U32.v pos + 5);
    let z = serialize32_bounded_integer_4 () y' b (pos `U32.add` 1ul) in
    let h' = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + 5)) 1;
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` 1ul) (B.loc_buffer_from_to b (pos `U32.add` 1ul) (pos `U32.add` 5ul)) h h' ;
    5ul // 1ul `U32.add` z
  end

#pop-options

inline_for_extraction
let serialize32_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
: Tot (serializer32 (serialize_bounded_der_length32 (vmin) (vmax)))
= fun (y' : bounded_int32 (vmin) (vmax)) #rrel #rel b pos ->
  serialize32_bounded_der_length32' vmin vmax y' b pos

inline_for_extraction
let write_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
: Tot (leaf_writer_strong (serialize_bounded_der_length32 (vmin) (vmax)))
= leaf_writer_strong_of_serializer32 (serialize32_bounded_der_length32 vmin vmax) ()
