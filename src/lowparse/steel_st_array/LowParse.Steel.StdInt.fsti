// TODO: replace with Steel.C.StdInt once FStar#2349 is merged
module LowParse.Steel.StdInt

open FStar.Mul

module U32 = FStar.UInt32
module I32 = FStar.Int32

inline_for_extraction noextract // TODO: replace with primitive extraction
val size_t : eqtype

val size_precond (x: nat) : Tot prop

noextract
val size_v (x: size_t) : Pure nat // should be Ghost, but need Pure to implement alloc
  (requires True)
  (ensures (fun y -> size_precond y))

val size_v_inj (x1 x2: size_t) : Lemma
  (size_v x1 == size_v x2 ==> x1 == x2)
  [SMTPat (size_v x1); SMTPat (size_v x2)]

inline_for_extraction noextract
val mk_size_t (x: U32.t) : Pure size_t
  (requires True)
  (ensures (fun y -> size_v y == U32.v x))

noextract
val int_to_size_t (x: nat) : Pure size_t // should be Ghost, but need Pure to implement array views
  (requires (size_precond x))
  (ensures (fun y -> size_v y == x))

val size_precond_le (x y: nat) : Lemma
  (requires (x <= y /\ size_precond y))
  (ensures (size_precond x))
  [SMTPat (size_precond x); SMTPat (size_precond y)]

val size_add (x y: size_t) : Pure size_t
  (requires (size_precond (size_v x + size_v y)))
  (ensures (fun z -> size_v z == size_v x + size_v y))

val size_sub (x y: size_t) : Pure size_t
  (requires (size_v x >= size_v y))
  (ensures (fun z -> size_v z == size_v x - size_v y))

val size_mul (x y: size_t) : Pure size_t
  (requires (size_precond (size_v x * size_v y)))
  (ensures (fun z -> size_v z == size_v x * size_v y))

val size_div (x y: size_t) : Pure size_t
  (requires (size_v y > 0))
  (ensures (fun z -> size_v z == size_v x / size_v y))

val size_le (x y: size_t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (size_v x <= size_v y)))

let size_lt (x y: size_t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (size_v x < size_v y)))
= not (size_le y x)

let zero_size : (zero_size: size_t { size_v zero_size == 0 }) = mk_size_t 0ul

let one_size : (zero_size: size_t { size_v zero_size == 1 }) = mk_size_t 1ul
