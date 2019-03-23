module LowParse.BigEndianImpl.Low
include LowParse.BigEndianImpl.Base

module U = FStar.UInt
module U8 = FStar.UInt8

module Seq = FStar.Seq
module U32 = FStar.UInt32
module M = LowParse.Math
module G = FStar.Ghost

module B = LowStar.Buffer
module MO = LowStar.ModifiesPat
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* TODO: generalize LowParse.BigEndianImpl.SLow.be_to_n_body' with a monad. (problem: we don't have effect polymorphism in F* ) *)

inline_for_extraction
val be_to_n_body'
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B.buffer U8.t)
  (len: U32.t)
  (i: U32.t)
  (accu: t)
: HST.Stack t
  (requires (fun h ->
    B.live h s /\
    0 < U32.v i /\
    U32.v i <= B.length s /\
    U32.v len == B.length s /\
    Prims.op_Multiply 8 (B.length s) <= n /\
    u.v accu == be_to_n (Seq.slice (B.as_seq h s) 0 (B.length s - U32.v i))
  ))
  (ensures (fun h accu' h' ->
    h == h' /\
    u.v accu' == be_to_n (Seq.slice (B.as_seq h s) 0 (B.length s - (U32.v i - 1)))
  ))

#reset-options "--z3rlimit 16"

let be_to_n_body' t n u s len i accu =
  match u with
  | UIntType u_v _ u_from_byte _ _ u_add u_mul256 _ ->
  let h = HST.get () in
  let sq0 = G.hide (B.as_seq h s) in
  let sq = G.hide (Seq.slice (G.reveal sq0) 0 (B.length s - U32.v i)) in
  let sq' = G.hide (Seq.slice (G.reveal sq0) 0 (B.length s - (U32.v i - 1))) in
  let b = B.index s (U32.sub len i) in
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
  (s: B.buffer U8.t)
: HST.Stack t
  (requires (fun h ->
    B.live h s /\
    B.length s == 1 /\
    Prims.op_Multiply 8 (B.length s) <= n
  ))
  (ensures (fun h accu' h' ->
    h == h' /\
    u.v accu' == be_to_n (B.as_seq h s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res =
    be_to_n_body' t n u s 1ul 1ul u_zero
  in
  res

inline_for_extraction
let be_to_n_2
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B.buffer U8.t)
: HST.Stack t
  (requires (fun h ->
    B.live h s /\
    B.length s == 2 /\
    Prims.op_Multiply 8 (B.length s) <= n
  ))
  (ensures (fun h accu' h' ->
    h == h' /\
    u.v accu' == be_to_n (B.as_seq h s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res2 =
    be_to_n_body' t n u s 2ul 2ul u_zero
  in
  let res1 =
    be_to_n_body' t n u s 2ul 1ul res2
  in
  res1

inline_for_extraction
let be_to_n_3
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B.buffer U8.t)
: HST.Stack t
  (requires (fun h ->
    B.live h s /\
    B.length s == 3 /\
    Prims.op_Multiply 8 (B.length s) <= n
  ))
  (ensures (fun h accu' h' ->
    h == h' /\
    u.v accu' == be_to_n (B.as_seq h s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res3 =
    be_to_n_body' t n u s 3ul 3ul u_zero
  in
  let res2 =
    be_to_n_body' t n u s 3ul 2ul res3
  in
  let res1 =
    be_to_n_body' t n u s 3ul 1ul res2
  in
  res1

inline_for_extraction
let be_to_n_4
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B.buffer U8.t)
: HST.Stack t
  (requires (fun h ->
    B.live h s /\
    B.length s == 4 /\
    Prims.op_Multiply 8 (B.length s) <= n
  ))
  (ensures (fun h accu' h' ->
    h == h' /\
    u.v accu' == be_to_n (B.as_seq h s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res4 =
    be_to_n_body' t n u s 4ul 4ul u_zero
  in
  let res3 =
    be_to_n_body' t n u s 4ul 3ul res4
  in
  let res2 =
    be_to_n_body' t n u s 4ul 2ul res3
  in
  let res1 =
    be_to_n_body' t n u s 4ul 1ul res2
  in
  res1

inline_for_extraction
val n_to_be_body'
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (len: U32.t)
  (x0: t)
  (i: U32.t)
  (x: t)
  (b: B.buffer U8.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    U32.v len == B.length b /\
    8 `Prims.op_Multiply` (U32.v len) <= n /\
    0 < U32.v i /\
    U32.v i <= U32.v len /\ (
    let accu = Seq.slice (B.as_seq h b) (U32.v i) (U32.v len) in
    u.v x0 < pow2 (8 `Prims.op_Multiply` U32.v len) /\
    u.v x < pow2 (8 `Prims.op_Multiply` U32.v i) /\
    n_to_be len (u.v x0) == Seq.append (n_to_be i (u.v x)) (accu)
  )))
  (ensures (fun h _ h' ->
    MO.modifies (MO.loc_buffer b) h h' /\
    B.live h' b /\ (
    let accu = Seq.slice (B.as_seq h b) (U32.v i) (U32.v len) in
    let x' = u.div256 x in
    let i' = U32.sub i 1ul in
    let accu' = Seq.slice (B.as_seq h' b) (U32.v i') (U32.v len) in
    u.v x' < pow2 (8 `Prims.op_Multiply` U32.v i') /\
    n_to_be len (u.v x0) == Seq.append (n_to_be i' (u.v x')) (accu')
  )))

let n_to_be_body' t n u len x0 i x b =
  match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let h = HST.get () in
  let bx = u_to_byte x in
  let i' = U32.sub i 1ul in
  B.upd b i' bx;
  M.pow2_plus 8 (8 `Prims.op_Multiply` U32.v i');
  let x' = G.hide (u_div256 x) in
  assert (u_v (G.reveal x') < pow2 (8 `Prims.op_Multiply` U32.v i'));
  assert (n_to_be i (u_v x) == Seq.append (n_to_be i' (u_v (G.reveal x'))) (Seq.create 1 bx));
  let h' = HST.get () in
  let accu = G.hide (Seq.slice (B.as_seq h b) (U32.v i) (U32.v len)) in
  let accu' = G.hide (Seq.slice (B.as_seq h' b) (U32.v i') (U32.v len)) in
  assert (G.reveal accu' `Seq.equal` Seq.append (Seq.create 1 bx) (G.reveal accu));
  Seq.append_assoc (n_to_be i' (u_v (G.reveal x'))) (Seq.create 1 bx) (G.reveal accu)

inline_for_extraction
let n_to_be_1
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
  (b: B.buffer U8.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    B.length b == 1 /\
    8 `Prims.op_Multiply` 1 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 1)
  ))
  (ensures (fun h _ h' ->
    MO.modifies (MO.loc_buffer b) h h' /\
    B.live h' b /\ (
    let accu' = B.as_seq h' b in
    n_to_be 1ul (u.v x0) == accu'
  )))
= Seq.append_empty_r (n_to_be 1ul (u.v x0));
  n_to_be_body' t n u 1ul x0 1ul x0 b;
  let h' = HST.get () in
  Seq.append_empty_l (B.as_seq h' b)

inline_for_extraction
let n_to_be_2
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
  (b: B.buffer U8.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    B.length b == 2 /\
    8 `Prims.op_Multiply` 2 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 2)
  ))
  (ensures (fun h _ h' ->
    MO.modifies (MO.loc_buffer b) h h' /\
    B.live h' b /\ (
    let accu' = B.as_seq h' b in
    n_to_be 2ul (u.v x0) == accu'
  )))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  Seq.append_empty_r (n_to_be 2ul (u.v x0));
  n_to_be_body' t n u 2ul x0 2ul x0 b;
  let x1 = u_div256 x0 in
  n_to_be_body' t n u 2ul x0 1ul x1 b;
  let h' = HST.get () in
  Seq.append_empty_l (B.as_seq h' b)

inline_for_extraction
let n_to_be_3
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
  (b: B.buffer U8.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    B.length b == 3 /\
    8 `Prims.op_Multiply` 3 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 3)
  ))
  (ensures (fun h _ h' ->
    MO.modifies (MO.loc_buffer b) h h' /\
    B.live h' b /\ (
    let accu' = B.as_seq h' b in
    n_to_be 3ul (u.v x0) == accu'
  )))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  Seq.append_empty_r (n_to_be 3ul (u.v x0));
  n_to_be_body' t n u 3ul x0 3ul x0 b;
  let x2 = u_div256 x0 in
  n_to_be_body' t n u 3ul x0 2ul x2 b;
  let x1 = u_div256 x2 in
  n_to_be_body' t n u 3ul x0 1ul x1 b;
  let h' = HST.get () in
  Seq.append_empty_l (B.as_seq h' b)

inline_for_extraction
let n_to_be_4
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
  (b: B.buffer U8.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    B.length b == 4 /\
    8 `Prims.op_Multiply` 4 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 4)
  ))
  (ensures (fun h _ h' ->
    MO.modifies (MO.loc_buffer b) h h' /\
    B.live h' b /\ (
    let accu' = B.as_seq h' b in
    n_to_be 4ul (u.v x0) == accu'
  )))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  Seq.append_empty_r (n_to_be 4ul (u.v x0));
  n_to_be_body' t n u 4ul x0 4ul x0 b;
  let x3 = u_div256 x0 in
  n_to_be_body' t n u 4ul x0 3ul x3 b;
  let x2 = u_div256 x3 in
  n_to_be_body' t n u 4ul x0 2ul x2 b;
  let x1 = u_div256 x2 in
  n_to_be_body' t n u 4ul x0 1ul x1 b;
  let h' = HST.get () in
  Seq.append_empty_l (B.as_seq h' b)
