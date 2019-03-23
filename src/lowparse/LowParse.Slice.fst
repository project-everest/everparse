module LowParse.Slice
open LowParse.Bytes

// TODO: this is only for truncate_slice, which could probably be replaced with
// truncated_slice, possibly needing an SMTPat
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module L = FStar.List.Tot

(*** Slices: buffers with runtime length *)

// a byte buffer type indexed by size
type lbuffer (len: nat) = b:B.buffer byte{B.length b == len}

// augment a buffer with a runtime length
private
noeq type bslice_ =
  | BSlice : len:U32.t -> p:lbuffer (U32.v len) -> bslice_

let bslice = bslice_

inline_for_extraction
let length (b: bslice) : Tot U32.t = b.len

inline_for_extraction
let as_buffer
  (b: bslice)
: Tot (lbuffer (U32.v (length b)))
= b.p

let of_buffer_spec
  (b: B.buffer byte)
  (len: U32.t)
: Ghost bslice
  (requires (U32.v len <= B.length b))
  (ensures (fun y ->
    U32.v len <= B.length b /\
    length y == len /\
    as_buffer y == B.sub b 0ul len
  ))
= BSlice len (B.sub b 0ul len)

let live h (b: bslice) = B.live h (as_buffer b)

let live_as_buffer (h: HS.mem) (b: bslice) : Lemma
  (live h b <==> B.live h (as_buffer b))
  [SMTPatOr [
    [SMTPat (live h b)];
    [SMTPat (B.live h (as_buffer b))]
  ]]
= ()

inline_for_extraction
let of_buffer
  (b: B.buffer byte)
  (len: U32.t)
: HST.Stack bslice
  (requires (fun h ->
    B.live h b /\
    U32.v len <= B.length b
  ))
  (ensures (fun h y h' ->
    h' == h /\
    U32.v len <= B.length b /\
    live h y /\
    y == of_buffer_spec b len
  ))
= let b' = B.sub b 0ul len in
  BSlice len b'

let as_seq h (b: bslice) : Ghost (s:bytes)
  (requires (live h b))
  (ensures (fun s -> Seq.length s == U32.v (length b))) = B.as_seq h (as_buffer b)

let length_as_seq h (b: bslice) : Lemma
  (requires (live h b))
  (ensures (Seq.length (as_seq h b) == U32.v (length b)))
  [SMTPat (Seq.length (as_seq h b))]
= ()

let length_as_buffer (b: bslice) : Lemma
  (B.length (as_buffer b) == U32.v (length b))
  [SMTPat (B.length (as_buffer b))]
= ()

let buffer_as_seq_as_buffer (h: HS.mem) (b: bslice) : Lemma
  (requires (live h b))
  (ensures (
    live h b /\
    B.live h (as_buffer b) /\
    B.as_seq h (as_buffer b) == as_seq h b
  ))
  [SMTPat (B.as_seq h (as_buffer b))]
= ()

inline_for_extraction
let index
  (b: bslice)
  (i: U32.t)
: HST.Stack byte
  (requires (fun h ->
    live h b /\
    U32.v i < U32.v (length b)
  ))
  (ensures (fun h v h' ->
    h' == h /\
    live h' b /\
    U32.v i < U32.v (length b) /\
    v == Seq.index (as_seq h b) (U32.v i)
  ))
= B.index (as_buffer b) i

let advanced_slice (b: bslice) (off:U32.t) : Ghost bslice
  (requires (U32.v off <= U32.v (length b)))
  (ensures (fun _ -> True))
= BSlice (U32.sub (length b) off) (B.sub (as_buffer b) off (U32.sub (length b) off))

let advanced_slice_zero (b: bslice) : Lemma
  (advanced_slice b 0ul == b)
  [SMTPat (advanced_slice b 0ul)]
= ()

inline_for_extraction
let advance_slice (b:bslice) (off:U32.t) : HST.Stack bslice
  (requires (fun h -> live h b /\ U32.v off <= U32.v (length b)))
  (ensures (fun h b' h' ->
    h' == h /\
    U32.v off <= U32.v (length b) /\
    b' == advanced_slice b off
  ))
= BSlice (U32.sub (length b) off) (B.sub (as_buffer b) off (U32.sub (length b) off))

let length_advanced_slice (b: bslice) (off: U32.t) : Lemma
  (requires (
    U32.v off <= U32.v (length b)
  ))
  (ensures (
    U32.v off <= U32.v (length b) /\
    length (advanced_slice b off) == U32.sub (length b) off
  ))
  [SMTPat (length (advanced_slice b off))]
= ()

let as_buffer_advanced_slice (b: bslice) (off: U32.t) : Lemma
  (requires (
    U32.v off <= U32.v (length b)
  ))
  (ensures (
    U32.v off <= U32.v (length b) /\
    as_buffer (advanced_slice b off) == B.sub (as_buffer b) off (U32.sub (length b) off)
  ))
//  [SMTPat (as_buffer (advanced_slice b off))] // does not typecheck
= ()

let as_buffer_advanced_slice' (b: bslice) (off: U32.t { U32.v off <= U32.v (length b) } ) : Lemma
  (ensures (
    as_buffer (advanced_slice b off) == B.sub (as_buffer b) off (U32.sub (length b) off)
  ))
  [SMTPat (as_buffer (advanced_slice b off))]
= ()

let live_advanced_slice (b: bslice) (off: U32.t) h:
  Lemma
  (requires (U32.v off <= U32.v (length b)))
  (ensures (U32.v off <= U32.v (length b) /\ (live h (advanced_slice b off) <==> live h b)))
  [SMTPat (live h (advanced_slice b off))]
= ()

let as_seq_advanced_slice (b:bslice) (off:U32.t) h :
  Lemma (requires (live h b /\ U32.v off <= U32.v (length b)))
        (ensures (
	  U32.v off <= U32.v (length b) /\
	  as_seq h (advanced_slice b off) == Seq.slice (as_seq h b) (U32.v off) (Seq.length (as_seq h b))
        ))
  [SMTPat (as_seq h (advanced_slice b off))]
= ()

let advanced_slice_advanced_slice
  (b: bslice)
  (off1: U32.t)
  (off2: U32.t)
: Lemma
  (requires (
    U32.v off1 <= U32.v (length b) /\
    U32.v off2 <= U32.v (U32.sub (length b) off1)
  ))
  (ensures (
    U32.v off1 <= U32.v (length b) /\
    U32.v off2 <= U32.v (U32.sub (length b) off1) /\
    advanced_slice (advanced_slice b off1) off2 == advanced_slice b (U32.add off1 off2)
  ))
  [SMTPat (advanced_slice (advanced_slice b off1) off2)]
= let s1 = advanced_slice b off1 in
  let s2 = advanced_slice s1 off2 in
  B.sub_sub (as_buffer b) off1 (length s1) off2 (length s2)

// pure version of truncate_slice (which is in Stack)
val truncated_slice : b:bslice -> len:U32.t -> Ghost bslice (requires (U32.v len <= U32.v (length b))) (ensures (fun _ -> True))
let truncated_slice b len = BSlice len (B.sub (as_buffer b) (U32.uint_to_t 0) len)

inline_for_extraction
val truncate_slice : b:bslice -> len:U32.t -> HST.Stack bslice
  (requires (fun h0 -> live h0 b /\ U32.v len <= U32.v (length b)))
  (ensures (fun h0 r h1 -> live h1 b /\
                        live h1 r /\
			U32.v len <= U32.v (length b) /\
                        h0 == h1 /\
			r == truncated_slice b len /\
                        as_seq h1 r == Seq.slice (as_seq h1 b) 0 (U32.v len)))
let truncate_slice b len = BSlice len (B.sub (as_buffer b) (U32.uint_to_t 0) len)

let as_buffer_truncated_slice
  (b: bslice)
  (len: U32.t)
: Lemma
  (requires (U32.v len <= U32.v (length b)))
  (ensures (U32.v len <= U32.v (length b) /\ as_buffer (truncated_slice b len) == B.sub (as_buffer b) 0ul len))
//  [SMTPat (as_buffer (truncated_slice b len))] // does not typecheck
= ()

let as_buffer_truncated_slice'
  (b: bslice)
  (len: U32.t {U32.v len <= U32.v (length b)} )
: Lemma
  (as_buffer (truncated_slice b len) == B.sub (as_buffer b) 0ul len)
  [SMTPat (as_buffer (truncated_slice b len))]
= ()

let length_truncated_slice
  (b: bslice)
  (len: U32.t)
: Lemma
  (requires (U32.v len <= U32.v (length b)))
  (ensures (U32.v len <= U32.v (length b) /\ length (truncated_slice b len) == len))
  [SMTPat (length (truncated_slice b len))]
= ()

let live_truncated_slice
  (h: HS.mem)
  (b: bslice)
  (len: U32.t)
: Lemma
  (requires (U32.v len <= U32.v (length b)))
  (ensures (
    U32.v len <= U32.v (length b) /\
    (live h (truncated_slice b len) <==> live h b)
  ))
  [SMTPat (live h (truncated_slice b len))]
= ()

let as_seq_truncated_slice
  (h: HS.mem)
  (b: bslice)
  (len: U32.t)
: Lemma
  (requires (U32.v len <= U32.v (length b) /\ live h b))
  (ensures (
    U32.v len <= U32.v (length b) /\
    live h b /\
    as_seq h (truncated_slice b len) == Seq.slice (as_seq h b) 0 (U32.v len)
  ))
  [SMTPat (as_seq h (truncated_slice b len))]
= ()

let truncated_slice_truncated_slice
  (b: bslice)
  (len1 len2: U32.t)
: Lemma
  (requires (
    U32.v len2 <= U32.v len1 /\
    U32.v len1 <= U32.v (length b)
  ))
  (ensures (
    U32.v len2 <= U32.v len1 /\
    U32.v len1 <= U32.v (length b) /\
    truncated_slice (truncated_slice b len1) len2 == truncated_slice b len2
  ))
  [SMTPat (truncated_slice (truncated_slice b len1) len2)]
= ()

let advanced_slice_truncated_slice
  (b: bslice)
  (len1 len2: U32.t)
: Lemma
  (requires (
    U32.v len2 <= U32.v len1 /\
    U32.v len1 <= U32.v (length b)
  ))
  (ensures (
    U32.v len2 <= U32.v len1 /\
    U32.v len1 <= U32.v (length b) /\
    advanced_slice (truncated_slice b len1) len2 == truncated_slice (advanced_slice b len2) (U32.sub len1 len2)
  ))
  [SMTPat (advanced_slice (truncated_slice b len1) len2)]
= ()

let truncated_slice_advanced_slice
  (b: bslice)
  (len1 len2: U32.t)
: Lemma
  (requires (
    U32.v len1 <= U32.v (length b) /\
    U32.v len2 <= U32.v (length b) - U32.v len1
  ))
  (ensures (
    U32.v len1 <= U32.v (length b) /\
    U32.v len2 <= U32.v (length b) - U32.v len1 /\
    truncated_slice (advanced_slice b len1) len2 == advanced_slice (truncated_slice b (U32.add len1 len2)) len1
  ))
  [SMTPat (truncated_slice (advanced_slice b len1) len2)]
= ()

let includes b b' = B.includes (as_buffer b) (as_buffer b')

let includes_trans (b1 b2 b3: bslice) : Lemma
  (requires (includes b1 b2 /\ includes b2 b3))
  (ensures (includes b1 b3))
= B.includes_trans (as_buffer b1) (as_buffer b2) (as_buffer b3)

let disjoint b b' = B.disjoint (as_buffer b) (as_buffer b')

let disjoint_includes (b1 b2 b1' b2' : bslice) : Lemma
  (requires (disjoint b1 b2 /\ includes b1 b1' /\ includes b2 b2'))
  (ensures (disjoint b1' b2'))
= ()

let includes_advanced_slice (b: bslice) (len: U32.t) : Lemma
  (requires (U32.v len <= U32.v (length b)))
  (ensures (U32.v len <= U32.v (length b) /\ includes b (advanced_slice b len)))
= ()

let includes_truncated_slice (b: bslice) (len: U32.t) : Lemma
  (requires (U32.v len <= U32.v (length b)))
  (ensures (U32.v len <= U32.v (length b) /\ includes b (truncated_slice b len)))
= ()

let disjoint_truncated_slice_advanced_slice
  (b: bslice)
  (len1 len2: U32.t)
: Lemma
  (requires (U32.v len1 <= U32.v len2 /\ U32.v len2 <= U32.v (length b)))
  (ensures (
    U32.v len1 <= U32.v len2 /\ U32.v len2 <= U32.v (length b) /\
    disjoint (truncated_slice b len1) (advanced_slice b len2)
  ))
= ()

(*! Framing slices *)

let modifies_none = B.modifies_none

(*! Splitting slices into two parts *)

let buffer_is_concat
  (#t: Type)
  (b: B.buffer t)
  (b1 b2: B.buffer t)
: GTot Type0
= B.length b == B.length b1 + B.length b2 /\
  b1 == B.sub b 0ul (U32.uint_to_t (B.length b1)) /\
  b2 == B.sub b (U32.uint_to_t (B.length b1)) (U32.uint_to_t (B.length b2))

let buffer_is_concat_intro
  (#t: Type)
  (b: B.buffer t)
  (i: U32.t)
: Lemma
  (requires (U32.v i <= B.length b))
  (ensures (
    U32.v i <= B.length b /\
    buffer_is_concat b (B.sub b 0ul i) (B.sub b i (U32.sub (U32.uint_to_t (B.length b)) i))
  ))
= ()

let buffer_is_concat_zero_l
  (#t: Type)
  (b: B.buffer t)
: Lemma
  (buffer_is_concat b (B.sub b 0ul 0ul) b)
= ()

let buffer_is_concat_zero_r
  (#t: Type)
  (b: B.buffer t)
: Lemma
  (buffer_is_concat b b (B.sub b (U32.uint_to_t (B.length b)) 0ul))
= ()

let buffer_is_concat_assoc
  (#t: Type)
  (b123 b12 b23 b1 b2 b3: B.buffer t)
: Lemma
  (requires (
    buffer_is_concat b12 b1 b2 /\
    buffer_is_concat b23 b2 b3
  ))
  (ensures (
    buffer_is_concat b123 b1 b23 <==> buffer_is_concat b123 b12 b3
  ))
= ()

let buffer_is_concat_live
  (#t: Type)
  (h: HS.mem)
  (b12 b1 b2: B.buffer t)
: Lemma
  (requires (
    buffer_is_concat b12 b1 b2 /\ (
    B.live h b1 \/
    B.live h b2 \/
    B.live h b12
  )))
  (ensures (
    B.live h b1 /\
    B.live h b2 /\
    B.live h b12
  ))
= ()

let is_concat
  (b: bslice)
  (b1 b2: bslice)
: GTot Type0
= U32.v (length b1) <= U32.v (length b) /\
  b1 == truncated_slice b (length b1) /\
  b2 == advanced_slice b (length b1)

let is_concat_intro
  (b: bslice)
  (i: U32.t)
: Lemma
  (requires (U32.v i <= U32.v (length b)))
  (ensures (
    U32.v i <= U32.v (length b) /\
    is_concat b (truncated_slice b i) (advanced_slice b i)
  ))
= ()

let is_concat_intro'
  (b b1 b2: bslice)
: Lemma
  (requires (buffer_is_concat (as_buffer b) (as_buffer b1) (as_buffer b2)))
  (ensures (is_concat b b1 b2))
= ()

#set-options "--z3rlimit 16"

let is_concat_assoc
  (b123 b12 b23 b1 b2 b3: bslice)
: Lemma
  (requires (
    is_concat b12 b1 b2 /\
    is_concat b23 b2 b3
  ))
  (ensures (
    is_concat b123 b1 b23 <==> is_concat b123 b12 b3
  ))
= ()

#reset-options

let is_concat_live
  (h: HS.mem)
  (b12 b1 b2: bslice)
: Lemma
  (requires (
    is_concat b12 b1 b2 /\ (
    live h b1 \/
    live h b2 \/
    live h b12
  )))
  (ensures (
    live h b1 /\
    live h b2 /\
    live h b12
  ))
= ()

let is_prefix (short long: bslice) : GTot Type0 =
  U32.v (length short) <= U32.v (length long) /\
  short == truncated_slice long (length short)

let is_prefix_refl (b: bslice) : Lemma (is_prefix b b) = ()

let is_prefix_truncated_slice
  (b: bslice)
  (i: U32.t)
: Lemma
  (requires (U32.v i <= U32.v (length b)))
  (ensures (
    U32.v i <= U32.v (length b) /\
    is_prefix (truncated_slice b i) b
  ))
= ()

let rec is_concat_gen
  (b: bslice)
  (l: list bslice)
: GTot Type0
  (decreases l)
= match l with
  | [] -> length b == 0ul
  | b1 :: q ->
    is_prefix b1 b /\ (
      let b' = advanced_slice b (length b1) in
      is_concat_gen b' q
    )

#set-options "--z3rlimit 16"

let is_concat_is_concat_gen
  (b b1 b2: bslice)
: Lemma
  (is_concat b b1 b2 <==> is_concat_gen b [b1; b2])
  [SMTPatOr [
    [SMTPat (is_concat b b1 b2)];
    [SMTPat (is_concat_gen b [b1; b2])];
  ]]
= ()

#reset-options

let is_prefix_is_concat_is_prefix
  (b b12 b1 b2: bslice)
: Lemma
  (requires (
    is_prefix b12 b /\
    is_concat b12 b1 b2
  ))
  (ensures (
    is_prefix b1 b
  ))
= ()

#set-options "--z3rlimit 16"

let advanced_slice_is_prefix
  (short long: bslice)
  (i: U32.t)
: Lemma
  (requires (
    U32.v i <= U32.v (length short) /\
    is_prefix short long
  ))
  (ensures (
    U32.v i <= U32.v (length short) /\
    U32.v i <= U32.v (length long) /\
    is_prefix (advanced_slice short i) (advanced_slice long i)
  ))
= ()

#reset-options

let is_concat_gen_cons
  (b: bslice)
  (b1: bslice)
  (q: list bslice)
: Lemma
  (requires (
    is_prefix b1 b /\ (
      let b' = advanced_slice b (length b1) in
      is_concat_gen b' q
  )))
  (ensures (is_concat_gen b (b1 :: q)))
= ()

#set-options "--z3rlimit 256"

let rec is_concat_gen_append_intro_l
  (b bl: bslice)
  (ll lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (bl :: lr) /\
    is_concat_gen bl ll
  ))
  (ensures (
    is_concat_gen b (L.append ll lr)
  ))
  (decreases ll)
= match ll with
  | [] -> ()
  | (b' :: ll') ->
    assert (U32.v (length bl) <= U32.v (length b));
    assert (U32.v (length b') <= U32.v (length bl));   
    assert (is_prefix bl b);
    let bl_ = advanced_slice bl (length b') in
    let b_ = advanced_slice b (length b') in
    is_concat_gen_append_intro_l b_ bl_ ll' lr

#reset-options

let rec is_concat_gen_append_intro
  (b bm: bslice)
  (ll lm lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (L.append ll (bm :: lr)) /\
    is_concat_gen bm lm
  ))
  (ensures (
    is_concat_gen b (L.append ll (L.append lm lr))
  ))
  (decreases ll)
= match ll with
  | [] -> is_concat_gen_append_intro_l b bm lm lr
  | b' :: ll' ->
    is_concat_gen_append_intro (advanced_slice b (length b')) bm ll' lm lr

#set-options "--z3rlimit 128"

let rec is_concat_gen_append_elim_l
  (b bl: bslice)
  (ll lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (L.append ll lr) /\
    is_concat_gen bl ll /\
    Cons? ll
  ))
  (ensures (
    is_concat_gen b (bl :: lr)
  ))
  (decreases ll)
= match ll with
  | [_] -> ()
  | (b' :: ll') ->
    let bl_ = advanced_slice bl (length b') in
    let b_ = advanced_slice b (length b') in
    is_concat_gen_append_elim_l b_ bl_ ll' lr

#reset-options

let rec is_concat_gen_append_elim
  (b bm: bslice)
  (ll lm lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (L.append ll (L.append lm lr)) /\
    is_concat_gen bm lm /\
    Cons? lm
  ))
  (ensures (
    is_concat_gen b (L.append ll (bm :: lr))
  ))
  (decreases ll)
= match ll with
  | [] -> is_concat_gen_append_elim_l b bm lm lr
  | b' :: ll' ->
    is_concat_gen_append_elim (advanced_slice b (length b')) bm ll' lm lr

let rec is_prefix_gen
  (l: list bslice)
  (b: bslice)
: GTot Type0
  (decreases l)
= match l with
  | [] -> True
  | (b' :: l') ->
    is_prefix b' b /\
    is_prefix_gen l' (advanced_slice b (length b'))

let is_prefix_is_prefix_gen
  (short long: bslice)
: Lemma
  (is_prefix short long <==> is_prefix_gen [short] long)
= ()

let rec is_concat_gen_is_prefix_gen
  (l: list bslice)
  (b: bslice)
: Lemma
  (requires (is_concat_gen b l))
  (ensures (is_prefix_gen l b))
= match l with
  | [] -> ()
  | b' :: l' ->
    is_concat_gen_is_prefix_gen l' (advanced_slice b (length b'))
