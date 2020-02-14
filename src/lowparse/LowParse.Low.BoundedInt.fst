module LowParse.Low.BoundedInt
open LowParse.Low.Combinators
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module E = LowParse.Endianness.BitFields
module BF = LowParse.BitFields
module LE = LowParse.Low.Endianness
module Cast = FStar.Int.Cast

friend LowParse.Spec.BoundedInt

inline_for_extraction
let mul256 (x: U16.t) : Tot (y: U32.t { U32.v y == 256 `Prims.op_Multiply` U16.v x }) =
  assert_norm (pow2 8 == 256);
  FStar.Math.Lemmas.pow2_lt_compat 32 24;
  FStar.Math.Lemmas.pow2_lt_compat 24 16;
  FStar.Math.Lemmas.pow2_lt_compat 16 8;
  FStar.Math.Lemmas.pow2_plus 8 16;
  FStar.Math.Lemmas.small_mod (U16.v x `Prims.op_Multiply` 256) (pow2 32);
  FStar.UInt.shift_left_value_lemma #32 (U16.v x) 8;
  Cast.uint16_to_uint32 x `U32.shift_left` 8ul

inline_for_extraction
let div256 (x: U32.t) : Tot (y: U32.t { U32.v y == U32.v x / 256 }) =
  assert_norm (pow2 8 == 256);
  FStar.UInt.shift_right_value_lemma #32 (U32.v x) 8;
  x `U32.shift_right` 8ul

(* bounded integers *)

let read_bounded_integer_1 () =
  [@inline_let]
  let _ =
    decode_bounded_integer_injective 1
  in
  make_total_constant_size_reader 1 1ul #(bounded_integer 1) (decode_bounded_integer 1) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    E.index_be_to_n (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 1)) 0;
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 1));
    let r = B.index input pos in
    Cast.uint8_to_uint32 r
  )

let read_bounded_integer_2 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 2
  in
  make_total_constant_size_reader 2 2ul #(bounded_integer 2) (decode_bounded_integer 2) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    let r = LE.load16_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) input pos in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 2));
    Cast.uint16_to_uint32 r
  )

#push-options "--z3rlimit 16"

let read_bounded_integer_3 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 3
  in
  make_total_constant_size_reader 3 3ul #(bounded_integer 3) (decode_bounded_integer 3) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 3)) 2;
    E.reveal_be_to_n (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 3));
    let lo = B.index input (pos `U32.add` 2ul) in
    let hi = LE.load16_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) input pos in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 2));
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 3));
    assert_norm (pow2 8 == 256);
    Cast.uint8_to_uint32 lo `U32.add` (mul256 hi)
  )

#pop-options

let read_bounded_integer_4 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 4
  in
  make_total_constant_size_reader 4 4ul #(bounded_integer 4) (decode_bounded_integer 4) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 4));
    LE.load32_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) input pos
  )

let read_bounded_integer_ct
  i #rrel #rel sl pos
= let h = HST.get () in
  valid_total_constant_size h (parse_bounded_integer (U32.v i)) (U32.v i) sl pos;
  valid_facts (parse_bounded_integer (U32.v i)) h sl pos;
  valid_total_constant_size h parse_u32 4 sl pos;
  valid_facts parse_u32 h sl pos;
  decode_bounded_integer_injective (U32.v i);
  parse_u32_spec (bytes_of_slice_from h sl pos);
  E.bitfield_be_to_n_slice (Seq.slice (bytes_of_slice_from h sl pos) 0 4) 0 (U32.v i);
  let r = LE.load32_be_i sl.base pos in
  BF.uint32.BF.get_bitfield_gen r (8ul `U32.mul` (4ul `U32.sub` i)) 32ul

let serialize32_bounded_integer_1 () =
  fun (v: bounded_integer 1) #rrel #rel out pos ->
  bounded_integer_prop_equiv 1 v;
  E.index_n_to_be 1 (U32.v v) 0;
  mbuffer_upd out (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 1)) pos (Cast.uint32_to_uint8 v);
  1ul

let serialize32_bounded_integer_2 () =
  fun (v: bounded_integer 2) #rrel #rel out pos ->
  bounded_integer_prop_equiv 2 v;
  let h = HST.get () in
  let v' = (Cast.uint32_to_uint16 v) in
  LE.writable_store_pre out (U32.v pos) 2 (fun s -> E.be_to_n s == U16.v v') h;
  LE.store16_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) out pos v';
  let h' = HST.get () in
  LE.store_post_modifies out (U32.v pos) 2 (fun s -> E.be_to_n s == U16.v v') h h';
  2ul

#push-options "--z3rlimit 16"

let serialize32_bounded_integer_3 () =
  fun (v: bounded_integer 3) #rrel #rel out pos ->
  bounded_integer_prop_equiv 3 v;
  E.reveal_n_to_be 3 (U32.v v);
  assert_norm (pow2 8 == 256);
  let lo = Cast.uint32_to_uint8 v in
  mbuffer_upd out (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 3)) (pos `U32.add` 2ul) lo;
  let hi' = div256 v in
  FStar.Math.Lemmas.small_mod (U32.v hi') (pow2 16);
  let hi = Cast.uint32_to_uint16 hi' in
  let h1 = HST.get () in
  LE.writable_weaken out (U32.v pos) (U32.v pos + 3) h1 (U32.v pos) (U32.v pos + 2);
  LE.writable_store_pre out (U32.v pos) 2 (fun s -> E.be_to_n s == U16.v hi) h1;
  LE.store16_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) out pos hi;
  let h2 = HST.get () in
  LE.store_post_modifies out (U32.v pos) 2 (fun s -> E.be_to_n s == U16.v hi) h1 h2;
  B.modifies_buffer_from_to_elim out (pos `U32.add` 2ul) (pos `U32.add` 3ul) (B.loc_buffer_from_to out pos (pos `U32.add` 2ul)) h1 h2;
  assert (Seq.slice (B.as_seq h2 out) (U32.v pos + 2) (U32.v pos + 3) `Seq.equal` Seq.create 1 lo);
  3ul

#pop-options

let serialize32_bounded_integer_4 () =
  fun (v: bounded_integer 4) #rrel #rel out pos ->
  bounded_integer_prop_equiv 4 v;
  let h = HST.get () in
  LE.writable_store_pre out (U32.v pos) 4 (fun s -> E.be_to_n s == U32.v v) h;
  LE.store32_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) out pos v;
  let h' = HST.get () in
  LE.store_post_modifies out (U32.v pos) 4 (fun s -> E.be_to_n s == U32.v v) h h';
  4ul

inline_for_extraction
let write_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (leaf_writer_strong (serialize_bounded_int32 (U32.v min32) (U32.v max32)))
= [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  write_synth
    (write_filter
      (write_bounded_integer sz)
      (in_bounds min max))
    (fun x -> (x <: bounded_int32 min max))
    (fun x -> x)
    (fun x -> x)
    ()

let write_bounded_int32_1
  min32 max32
= write_bounded_int32' min32 max32 1

let write_bounded_int32_2
  min32 max32
= write_bounded_int32' min32 max32 2

let write_bounded_int32_3
  min32 max32
= write_bounded_int32' min32 max32 3

let write_bounded_int32_4
  min32 max32
= write_bounded_int32' min32 max32 4

inline_for_extraction
let read_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (leaf_reader (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= 
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  read_inline_synth
    (parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (fun x -> (x <: bounded_int32 min max))
    (fun x -> x)
    (read_filter
      (read_bounded_integer sz)
      (in_bounds min max))
    ()

let read_bounded_int32_1
  min32 max32
= read_bounded_int32' min32 max32 1

let read_bounded_int32_2
  min32 max32
= read_bounded_int32' min32 max32 2

let read_bounded_int32_3
  min32 max32
= read_bounded_int32' min32 max32 3

let read_bounded_int32_4
  min32 max32
= read_bounded_int32' min32 max32 4

inline_for_extraction
let validate_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (validator (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= 
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  validate_synth
    (validate_filter
      (validate_bounded_integer sz)
      (read_bounded_integer sz)
      (in_bounds min max)
      (fun x -> not (x `U32.lt` min32 || max32 `U32.lt` x))
      )
    (fun x -> (x <: bounded_int32 min max))
    ()

let validate_bounded_int32_1
  min32 max32
= validate_bounded_int32' min32 max32 1

let validate_bounded_int32_2
  min32 max32
= validate_bounded_int32' min32 max32 2

let validate_bounded_int32_3
  min32 max32
= validate_bounded_int32' min32 max32 3

let validate_bounded_int32_4
  min32 max32
= validate_bounded_int32' min32 max32 4

inline_for_extraction
let jump_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= 
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  jump_synth
    (jump_filter
      (jump_bounded_integer sz)
      (in_bounds min max))
    (fun x -> (x <: bounded_int32 min max))
    ()

let jump_bounded_int32_1
  min32 max32
= jump_bounded_int32' min32 max32 1

let jump_bounded_int32_2
  min32 max32
= jump_bounded_int32' min32 max32 2

let jump_bounded_int32_3
  min32 max32
= jump_bounded_int32' min32 max32 3

let jump_bounded_int32_4
  min32 max32
= jump_bounded_int32' min32 max32 4


let read_bounded_integer_le_1 =
  [@inline_let] let _ = bounded_integer_of_le_injective 1 in
  make_total_constant_size_reader 1 1ul #(bounded_integer 1) (bounded_integer_of_le 1) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    E.index_le_to_n (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 1)) 0;
    E.lemma_le_to_n_is_bounded (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 1));
    let r = B.index b pos in
    Cast.uint8_to_uint32 r
  )

let read_bounded_integer_le_2 =
  [@inline_let] let _ = bounded_integer_of_le_injective 2 in
  make_total_constant_size_reader 2 2ul #(bounded_integer 2) (bounded_integer_of_le 2) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    let r = LE.load16_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos in
    E.lemma_le_to_n_is_bounded (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 2));
    Cast.uint16_to_uint32 r
  )

#push-options "--z3rlimit 16"

let read_bounded_integer_le_3 =
  [@inline_let] let _ = bounded_integer_of_le_injective 3 in
  make_total_constant_size_reader 3 3ul #(bounded_integer 3) (bounded_integer_of_le 3) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 3)) 1;
    E.reveal_le_to_n (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 3));
    let lo = B.index b pos in
    let hi = LE.load16_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b (pos `U32.add` 1ul) in
    E.lemma_le_to_n_is_bounded (Seq.slice (B.as_seq h b) (U32.v pos + 1) (U32.v pos + 3));
    E.lemma_le_to_n_is_bounded (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 3));
    assert_norm (pow2 8 == 256);
    Cast.uint8_to_uint32 lo `U32.add` (mul256 hi)
  )

#pop-options

let read_bounded_integer_le_4 =
  [@inline_let] let _ = bounded_integer_of_le_injective 4 in
  make_total_constant_size_reader 4 4ul #(bounded_integer 4) (bounded_integer_of_le 4) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    E.lemma_le_to_n_is_bounded (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 4));
    LE.load32_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos
  )

let read_u16_le =
  [@inline_let] let _ = synth_u16_le_injective in
  read_inline_synth'
    _
    synth_u16_le
    read_bounded_integer_le_2
    ()

let read_u32_le =
  read_inline_synth'
    _
    synth_u32_le
    read_bounded_integer_le_4
    ()

let serialize32_bounded_integer_le_1
= fun x #rrel #rel b pos ->
  bounded_integer_prop_equiv 1 x;
  E.index_n_to_le 1 (U32.v x) 0;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 1)) pos (Cast.uint32_to_uint8 x);
  1ul

let write_bounded_integer_le_1
= leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_1 ()

let serialize32_bounded_integer_le_2
= fun x #rrel #rel b pos ->
  bounded_integer_prop_equiv 2 x;
  let h = HST.get () in
  let x' = (Cast.uint32_to_uint16 x) in
  LE.writable_store_pre b (U32.v pos) 2 (fun s -> E.le_to_n s == U16.v x') h;
  LE.store16_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos x';
  let h' = HST.get () in
  LE.store_post_modifies b (U32.v pos) 2 (fun s -> E.le_to_n s == U16.v x') h h';
  2ul

let write_bounded_integer_le_2 = leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_2 ()

#push-options "--z3rlimit 16"

let serialize32_bounded_integer_le_3
= fun v #rrel #rel out pos ->
  bounded_integer_prop_equiv 3 v;
  E.reveal_n_to_le 3 (U32.v v);
  assert_norm (pow2 8 == 256);
  let lo = Cast.uint32_to_uint8 v in
  mbuffer_upd out (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 3)) pos lo;
  let hi' = div256 v in
  FStar.Math.Lemmas.small_mod (U32.v hi') (pow2 16);
  let hi = Cast.uint32_to_uint16 hi' in
  let h1 = HST.get () in
  LE.writable_weaken out (U32.v pos) (U32.v pos + 3) h1 (U32.v pos + 1) (U32.v pos + 3);
  LE.writable_store_pre out (U32.v pos + 1) 2 (fun s -> E.le_to_n s == U16.v hi) h1;
  LE.store16_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) out (pos `U32.add` 1ul) hi;
  let h2 = HST.get () in
  LE.store_post_modifies out (U32.v pos + 1) 2 (fun s -> E.le_to_n s == U16.v hi) h1 h2;
  B.modifies_buffer_from_to_elim out pos (pos `U32.add` 1ul) (B.loc_buffer_from_to out (pos `U32.add` 1ul) (pos `U32.add` 3ul)) h1 h2;
  assert (Seq.slice (B.as_seq h2 out) (U32.v pos) (U32.v pos + 1) `Seq.equal` Seq.create 1 lo);
  3ul

#pop-options

let write_bounded_integer_le_3 = leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_3 ()

let serialize32_bounded_integer_le_4
= fun v #rrel #rel out pos ->
  bounded_integer_prop_equiv 4 v;
  let h = HST.get () in
  LE.writable_store_pre out (U32.v pos) 4 (fun s -> E.le_to_n s == U32.v v) h;
  LE.store32_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) out pos v;
  let h' = HST.get () in
  LE.store_post_modifies out (U32.v pos) 4 (fun s -> E.le_to_n s == U32.v v) h h';
  4ul

let write_bounded_integer_le_4 = leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_4 ()

let write_u16_le =
  [@inline_let] let _ = synth_u16_le_injective; synth_u16_le_inverse in
  write_synth write_bounded_integer_le_2 synth_u16_le synth_u16_le_recip (fun x -> synth_u16_le_recip x) ()

let write_u32_le =
  write_synth write_bounded_integer_le_4 synth_u32_le synth_u32_le_recip (fun x -> synth_u32_le_recip x) ()

inline_for_extraction
let validate_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (validator (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= 
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  validate_synth
    (validate_filter
      (validate_bounded_integer_le sz)
      (read_bounded_integer_le sz)
      (in_bounds min max)
      (fun x -> not (x `U32.lt` min32 || max32 `U32.lt` x))
      )
    (fun x -> (x <: bounded_int32 min max))
    ()

let validate_bounded_int32_le_1
  min32 max32
= validate_bounded_int32_le' min32 max32 1

let validate_bounded_int32_le_2
  min32 max32
= validate_bounded_int32_le' min32 max32 2

let validate_bounded_int32_le_3
  min32 max32
= validate_bounded_int32_le' min32 max32 3

let validate_bounded_int32_le_4
  min32 max32
= validate_bounded_int32_le' min32 max32 4

inline_for_extraction
let jump_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= 
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  jump_synth
    (jump_filter
      (jump_bounded_integer_le sz)
      (in_bounds min max))
    (fun x -> (x <: bounded_int32 min max))
    ()

let jump_bounded_int32_le_1
  min32 max32
= jump_bounded_int32_le' min32 max32 1

let jump_bounded_int32_le_2
  min32 max32
= jump_bounded_int32_le' min32 max32 2

let jump_bounded_int32_le_3
  min32 max32
= jump_bounded_int32_le' min32 max32 3

let jump_bounded_int32_le_4
  min32 max32
= jump_bounded_int32_le' min32 max32 4

inline_for_extraction
let write_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (leaf_writer_strong (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))
= [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  write_synth
    (write_filter
      (write_bounded_integer_le sz)
      (in_bounds min max))
    (fun x -> (x <: bounded_int32 min max))
    (fun x -> x)
    (fun x -> x)
    ()

let write_bounded_int32_le_1
  min32 max32
= write_bounded_int32_le' min32 max32 1

let write_bounded_int32_le_2
  min32 max32
= write_bounded_int32_le' min32 max32 2

let write_bounded_int32_le_3
  min32 max32
= write_bounded_int32_le' min32 max32 3

let write_bounded_int32_le_4
  min32 max32
= write_bounded_int32_le' min32 max32 4

inline_for_extraction
let read_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz: nat { sz == log256' (U32.v max32) })
: Tot (leaf_reader (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= 
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  read_inline_synth
    (parse_filter (parse_bounded_integer_le sz) (in_bounds min max))
    (fun x -> (x <: bounded_int32 min max))
    (fun x -> x)
    (read_filter
      (read_bounded_integer_le sz)
      (in_bounds min max))
    ()

let read_bounded_int32_le_1
  min32 max32
= read_bounded_int32_le' min32 max32 1

let read_bounded_int32_le_2
  min32 max32
= read_bounded_int32_le' min32 max32 2

let read_bounded_int32_le_3
  min32 max32
= read_bounded_int32_le' min32 max32 3

let read_bounded_int32_le_4
  min32 max32
= read_bounded_int32_le' min32 max32 4

let validate_bounded_int32_le_fixed_size
  min32 max32
= validate_filter (validate_u32_le ()) read_u32_le (in_bounds (U32.v min32) (U32.v max32)) (fun x -> not (x `U32.lt` min32 || max32 `U32.lt` x))

let read_bounded_int32_le_fixed_size
  min32 max32
= read_filter read_u32_le (in_bounds (U32.v min32) (U32.v max32))

let write_bounded_int32_le_fixed_size
  min32 max32
= write_filter write_u32_le (in_bounds (U32.v min32) (U32.v max32))
