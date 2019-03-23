module LowParse.BigEndianImpl.SLow
include LowParse.BigEndianImpl.Base

module Seq = FStar.Seq
module B32 = LowParse.Bytes32
module U32 = FStar.UInt32
module M = LowParse.Math
module G = FStar.Ghost

#reset-options "--z3rlimit 16"

inline_for_extraction
let be_to_n_body'
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.bytes)
  (i: U32.t)
  (accu: t)
: Pure t
  (requires (
    0 < U32.v i /\
    U32.v i <= B32.length s /\
    Prims.op_Multiply 8 (B32.length s) <= n /\
    u.v accu == be_to_n (Seq.slice (B32.reveal s) 0 (B32.length s - U32.v i))
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (Seq.slice (B32.reveal s) 0 (B32.length s - (U32.v i - 1)))
  ))
= match u with
  | UIntType u_v _ u_from_byte _ _ u_add u_mul256 _ ->
  let sq = G.hide (Seq.slice (B32.reveal s) 0 (B32.length s - U32.v i)) in
  let sq' = G.hide (Seq.slice (B32.reveal s) 0 (B32.length s - (U32.v i - 1))) in
  let b = B32.get s (U32.sub (B32.len s) i) in
  assert (b == Seq.last (G.reveal sq'));
  assert (Seq.slice (G.reveal sq') 0 (Seq.length (G.reveal sq') - 1) == G.reveal sq);
  lemma_be_to_n_is_bounded (G.reveal sq);
  M.pow2_plus (8 `Prims.op_Multiply` Seq.length (G.reveal sq)) 8;
  assert (u_v accu `Prims.op_Multiply` 256 < pow2 (8 `Prims.op_Multiply` Seq.length (G.reveal sq) + 8));
  M.pow2_le_compat n (8 `Prims.op_Multiply` Seq.length (G.reveal sq) + 8);
  assert (u_v accu `Prims.op_Multiply` 256 < pow2 n);
  let accu256 = u_mul256 accu in
  let accu' = u_add (u_from_byte b) accu256 in
  accu'

inline_for_extraction
let be_to_n_1
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 1)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res =
    be_to_n_body' t n u s 1ul u_zero
  in
  res

inline_for_extraction
let be_to_n_2
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 2)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res2 =
    be_to_n_body' t n u s 2ul u_zero
  in
  let res1 =
    be_to_n_body' t n u s 1ul res2
  in
  res1

inline_for_extraction
let be_to_n_3
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 3)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res3 =
    be_to_n_body' t n u s 3ul u_zero
  in
  let res2 =
    be_to_n_body' t n u s 2ul res3
  in
  let res1 =
    be_to_n_body' t n u s 1ul res2
  in
  res1

inline_for_extraction
let be_to_n_4
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 4)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res4 =
    be_to_n_body' t n u s 4ul u_zero
  in
  let res3 =
    be_to_n_body' t n u s 3ul res4
  in
  let res2 =
    be_to_n_body' t n u s 2ul res3
  in
  let res1 =
    be_to_n_body' t n u s 1ul res2
  in
  res1


inline_for_extraction
let n_to_be_body'
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (len: U32.t)
  (x0: t)
  (i: U32.t)
  (x: t)
  (accu: B32.bytes)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` (U32.v len) <= n /\
    B32.length accu + U32.v i == U32.v len /\
    0 < U32.v i /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` U32.v len) /\
    u.v x < pow2 (8 `Prims.op_Multiply` U32.v i) /\
    n_to_be len (u.v x0) == Seq.append (n_to_be i (u.v x)) (B32.reveal accu)
  ))
  (ensures (fun accu' ->
    let x' = u.div256 x in
    let i' = U32.sub i 1ul in
    B32.length accu' + U32.v i' == U32.v len /\
    u.v x' < pow2 (8 `Prims.op_Multiply` U32.v i') /\
    n_to_be len (u.v x0) == Seq.append (n_to_be i' (u.v x')) (B32.reveal accu')
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let b = u_to_byte x in
  let i' = U32.sub i 1ul in
  let accu' = B32.append (B32.create 1ul b) accu in
  M.pow2_plus 8 (8 `Prims.op_Multiply` U32.v i');
  let x' = G.hide (u_div256 x) in
  assert (u_v (G.reveal x') < pow2 (8 `Prims.op_Multiply` U32.v i'));
  assert (n_to_be i (u_v x) == Seq.append (n_to_be i' (u_v (G.reveal x'))) (Seq.create 1 b));
  assert (B32.reveal accu' == Seq.append (Seq.create 1 b) (B32.reveal accu));
  Seq.append_assoc (n_to_be i' (u_v (G.reveal x'))) (Seq.create 1 b) (B32.reveal accu);
  accu'

inline_for_extraction
let n_to_be_1
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 1 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 1)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 1 /\
    n_to_be 1ul (u.v x0) == B32.reveal accu'
  ))
= let accu = B32.empty_bytes in
  B32.reveal_empty ();
  Seq.append_empty_r (n_to_be 1ul (u.v x0));
  let res = n_to_be_body' t n u 1ul x0 1ul x0 accu in
  Seq.append_empty_l (B32.reveal res);
  res

inline_for_extraction
let n_to_be_2
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 2 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 2)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 2 /\
    n_to_be 2ul (u.v x0) == B32.reveal accu'
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let accu = B32.empty_bytes in
  B32.reveal_empty ();
  Seq.append_empty_r (n_to_be 2ul (u.v x0));
  let accu1 = n_to_be_body' t n u 2ul x0 2ul x0 accu in
  let x1 = u_div256 x0 in
  let res = n_to_be_body' t n u 2ul x0 1ul x1 accu1 in
  Seq.append_empty_l (B32.reveal res);
  res

inline_for_extraction
let n_to_be_3
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 3 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 3)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 3 /\
    n_to_be 3ul (u.v x0) == B32.reveal accu'
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let accu = B32.empty_bytes in
  B32.reveal_empty ();
  Seq.append_empty_r (n_to_be 3ul (u.v x0));
  let accu2 = n_to_be_body' t n u 3ul x0 3ul x0 accu in
  let x2 = u_div256 x0 in
  let accu1 = n_to_be_body' t n u 3ul x0 2ul x2 accu2 in
  let x1 = u_div256 x2 in
  let res = n_to_be_body' t n u 3ul x0 1ul x1 accu1 in
  Seq.append_empty_l (B32.reveal res);
  res

inline_for_extraction
let n_to_be_4
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 4 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 4)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 4 /\
    n_to_be 4ul (u.v x0) == B32.reveal accu'
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let accu = B32.empty_bytes in
  B32.reveal_empty ();
  Seq.append_empty_r (n_to_be 4ul (u.v x0));
  let accu3 = n_to_be_body' t n u 4ul x0 4ul x0 accu in
  let x3 = u_div256 x0 in
  let accu2 = n_to_be_body' t n u 4ul x0 3ul x3 accu3 in
  let x2 = u_div256 x3 in
  let accu1 = n_to_be_body' t n u 4ul x0 2ul x2 accu2 in
  let x1 = u_div256 x2 in
  let res = n_to_be_body' t n u 4ul x0 1ul x1 accu1 in
  Seq.append_empty_l (B32.reveal res);
  res
