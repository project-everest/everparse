module LowParse.Low.ConstInt32

(* LowParse implementation module for 32 bits contants *)

include FStar.Endianness

include LowParse.Spec.ConstInt32
include LowParse.Spec.Int32le
include LowParse.Low.Combinators
include LowParse.Low.Int32le

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

let valid_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 } )
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma (valid (parse_constint32le v) h input pos 
    <==> 
    (valid parse_int32le h input pos /\
    U32.v (contents parse_int32le h input pos) == v))
= valid_facts (parse_constint32le v) h input pos;
  valid_facts parse_int32le h input pos;
  parse_constint32le_unfold v (bytes_of_slice_from h input pos)

inline_for_extraction
let validate_constint32le_slow
  (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
: Tot (validator (parse_constint32le (U32.v v)))
= fun #rrel #rel (input: slice rrel rel) pos ->
  let h = HST.get() in
    let _ =
      valid_constint32le (U32.v v) h input (uint64_to_uint32 pos);    
      valid_equiv parse_int32le h input (uint64_to_uint32 pos)
    in
  if U64.lt (Cast.uint32_to_uint64 input.len `U64.sub` pos) 4uL
  then
    validator_error_not_enough_data
  else
    let v' = read_int32le input (uint64_to_uint32 pos) in
    if U32.eq v v' then
      pos `U64.add` 4uL
    else
      validator_error_generic

inline_for_extraction
let read_constint32le 
  (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
: Tot (leaf_reader (parse_constint32le (U32.v v)))
= fun #rrel #rel input pos ->
    v

inline_for_extraction
let decompose_int32le_0
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (b0: nat { 0 <= b0 /\ b0 < 256 } )
= v % 256

inline_for_extraction
let decompose_int32le_1
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (b1: nat { 0 <= b1 /\ b1 < 256 } )
= v / 256 % 256

inline_for_extraction
let decompose_int32le_2
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (b2: nat { 0 <= b2 /\ b2 < 256 } )
= v / 65536 % 256

inline_for_extraction
let decompose_int32le_3
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (b3: nat { 0 <= b3 /\ b3 < 256 } )
= v / 16777216

let compose_int32le
  (b0: nat { 0 <= b0 /\ b0 < 256 } )
  (b1: nat { 0 <= b1 /\ b1 < 256 } )
  (b2: nat { 0 <= b2 /\ b2 < 256 } )
  (b3: nat { 0 <= b3 /\ b3 < 256 } )
: Tot (v: nat { 0 <= v /\ v < 4294967296 } ) 
= b0 
  + 256 `FStar.Mul.op_Star` (b1
  + 256 `FStar.Mul.op_Star` (b2
  + 256 `FStar.Mul.op_Star` b3))

#push-options "--z3rlimit 16"

let decompose_compose_equiv
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Lemma (compose_int32le (decompose_int32le_0 v) (decompose_int32le_1 v) (decompose_int32le_2 v) (decompose_int32le_3 v) == v)
= ()

#pop-options

inline_for_extraction
let compare_by_bytes
  (a0: U8.t { 0 <= U8.v a0 /\ U8.v a0 < 256 } )
  (a1: U8.t { 0 <= U8.v a1 /\ U8.v a1 < 256 } )
  (a2: U8.t { 0 <= U8.v a2 /\ U8.v a2 < 256 } )
  (a3: U8.t { 0 <= U8.v a3 /\ U8.v a3 < 256 } )
  (b0: U8.t { 0 <= U8.v b0 /\ U8.v b0 < 256 } )
  (b1: U8.t { 0 <= U8.v b1 /\ U8.v b1 < 256 } )
  (b2: U8.t { 0 <= U8.v b2 /\ U8.v b2 < 256 } )
  (b3: U8.t { 0 <= U8.v b3 /\ U8.v b3 < 256 } )
= a0 = b0 && a1 = b1 && a2 = b2 && a3 = b3

let compare_by_bytes'
  (a0: U8.t { 0 <= U8.v a0 /\ U8.v a0 < 256 } )
  (a1: U8.t { 0 <= U8.v a1 /\ U8.v a1 < 256 } )
  (a2: U8.t { 0 <= U8.v a2 /\ U8.v a2 < 256 } )
  (a3: U8.t { 0 <= U8.v a3 /\ U8.v a3 < 256 } )
  (b0: U8.t { 0 <= U8.v b0 /\ U8.v b0 < 256 } )
  (b1: U8.t { 0 <= U8.v b1 /\ U8.v b1 < 256 } )
  (b2: U8.t { 0 <= U8.v b2 /\ U8.v b2 < 256 } )
  (b3: U8.t { 0 <= U8.v b3 /\ U8.v b3 < 256 } )
= (compose_int32le (U8.v a0) (U8.v a1) (U8.v a2) (U8.v a3)) =
  (compose_int32le (U8.v b0) (U8.v b1) (U8.v b2) (U8.v b3))

#push-options "--max_fuel 5 --z3rlimit 64"

let compare_by_bytes_equiv
  (a0: U8.t { 0 <= U8.v a0 /\ U8.v a0 < 256 } )
  (a1: U8.t { 0 <= U8.v a1 /\ U8.v a1 < 256 } )
  (a2: U8.t { 0 <= U8.v a2 /\ U8.v a2 < 256 } )
  (a3: U8.t { 0 <= U8.v a3 /\ U8.v a3 < 256 } )
  (b0: U8.t { 0 <= U8.v b0 /\ U8.v b0 < 256 } )
  (b1: U8.t { 0 <= U8.v b1 /\ U8.v b1 < 256 } )
  (b2: U8.t { 0 <= U8.v b2 /\ U8.v b2 < 256 } )
  (b3: U8.t { 0 <= U8.v b3 /\ U8.v b3 < 256 } )
: Lemma 
  ((compare_by_bytes a0 a1 a2 a3 b0 b1 b2 b3) ==
    compare_by_bytes' a0 a1 a2 a3 b0 b1 b2 b3)
= let a = compose_int32le (U8.v a0) (U8.v a1) (U8.v a2) (U8.v a3) in
  let b = compose_int32le (U8.v b0) (U8.v b1) (U8.v b2) (U8.v b3) in
  decompose_compose_equiv a;
  decompose_compose_equiv b

#pop-options

let decompose_compare
  (v1 : nat { 0 <= v1 /\ v1 < 4294967296 } )
  (v2 : nat { 0 <= v2 /\ v2 < 4294967296 } )
: Lemma ( (v1 = v2) 
    == (compare_by_bytes
      (U8.uint_to_t (decompose_int32le_0 v1))
      (U8.uint_to_t (decompose_int32le_1 v1))
      (U8.uint_to_t (decompose_int32le_2 v1))
      (U8.uint_to_t (decompose_int32le_3 v1))
      (U8.uint_to_t (decompose_int32le_0 v2))
      (U8.uint_to_t (decompose_int32le_1 v2))
      (U8.uint_to_t (decompose_int32le_2 v2))
      (U8.uint_to_t (decompose_int32le_3 v2))))
= let a0 = U8.uint_to_t (decompose_int32le_0 v1) in
  let a1 = U8.uint_to_t (decompose_int32le_1 v1) in
  let a2 = U8.uint_to_t (decompose_int32le_2 v1) in
  let a3 = U8.uint_to_t (decompose_int32le_3 v1) in
  let b0 = U8.uint_to_t (decompose_int32le_0 v2) in
  let b1 = U8.uint_to_t (decompose_int32le_1 v2) in
  let b2 = U8.uint_to_t (decompose_int32le_2 v2) in
  let b3 = U8.uint_to_t (decompose_int32le_3 v2) in
  compare_by_bytes_equiv a0 a1 a2 a3 b0 b1 b2 b3;
  decompose_compose_equiv v1;
  decompose_compose_equiv v2


#push-options " --max_fuel 6 --z3rlimit 64 "

inline_for_extraction
let inplace_compare
  (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
  (#rrel: _)
  (#rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack bool
  (requires (fun h -> valid parse_int32le h input pos))
  (ensures (fun h res h' -> 
    B.modifies B.loc_none h h' /\
    res == (U32.eq (contents parse_int32le h input pos) v)))
= let h = HST.get () in
  let b = input.base in
  [@inline_let] let _ = 
    decode_int32le_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 4));
    decode_int32le_total_constant ();
    valid_facts parse_int32le h input pos;
    [@inline_let] let v' = contents parse_int32le h input pos in
    decompose_compose_equiv (U32.v v);
    decompose_compose_equiv (U32.v v');
    decompose_compare (U32.v v) (U32.v v')
  in
  let r0 = B.index b pos in
  let r1 = B.index b (pos `U32.add` 1ul) in
  let r2 = B.index b (pos `U32.add` 2ul) in
  let r3 = B.index b (pos `U32.add` 3ul) in
  [@inline_let] let b0 = U8.uint_to_t (decompose_int32le_0 (U32.v v)) in
  [@inline_let] let b1 = U8.uint_to_t (decompose_int32le_1 (U32.v v)) in
  [@inline_let] let b2 = U8.uint_to_t (decompose_int32le_2 (U32.v v)) in
  [@inline_let] let b3 = U8.uint_to_t (decompose_int32le_3 (U32.v v)) in
  compare_by_bytes r0 r1 r2 r3 b0 b1 b2 b3

#pop-options

inline_for_extraction
let validate_constint32le
  (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
: Tot (validator (parse_constint32le (U32.v v)))
= fun #rrel #rel (input: slice rrel rel) pos ->
  let h = HST.get() in
    let _ =
      valid_constint32le (U32.v v) h input (uint64_to_uint32 pos);    
      valid_equiv parse_int32le h input (uint64_to_uint32 pos)
    in
  if U64.lt (Cast.uint32_to_uint64 input.len `U64.sub` pos) 4uL
  then
    validator_error_not_enough_data
  else
    if inplace_compare v input (uint64_to_uint32 pos) then
      pos `U64.add` 4uL
    else
      validator_error_generic
