module LowParse.Math
include FStar.Math.Lemmas
open FStar.Mul

let mul_reg_r
  (a b x: int)
: Lemma
  (requires (
    x <> 0 /\
    a * x == b * x
  ))
  (ensures (a == b))
= ()

let mul_reg_l
  (x a b: int)
: Lemma
  (requires (
    x <> 0 /\
    x * a == x * b
  ))
  (ensures (a == b))
= ()

let lt_mul_add_reg_r
  (x y: nat)
  (s: pos)
: Lemma
  (requires (x * s < y * s + s))
  (ensures (x <= y))
= distributivity_add_left x (y + 1) s

let mult_decomp
  (i: pos) (j: nat)
: Lemma
  (i * j == j + (i - 1) * j)
= ()

let lemma_div_pow2_le (a: int) (n m: nat) : Lemma
  (requires (m <= n /\ a <= pow2 n))
  (ensures (m <= n /\ a <= pow2 n /\ a / pow2 m <= pow2 (n - m)))
= if a = pow2 n
  then pow2_multiplication_division_lemma_1 1 m n
  else lemma_div_lt a n m

let lemma_div_pow2_ge (a: int) (n m: nat) : Lemma
  (requires (m <= n /\ pow2 n <= a))
  (ensures (pow2 (n - m) <= a / pow2 m))
= pow2_multiplication_division_lemma_1 1 m n;
  lemma_div_le (pow2 n) a (pow2 m)

let pow2_le_recip
  (a b: nat)
: Lemma
  (requires (pow2 a <= pow2 b))
  (ensures (a <= b))
= Classical.move_requires (pow2_lt_compat a) b

let pow2_lt_recip
  (a b: nat)
: Lemma
  (requires (pow2 a < pow2 b))
  (ensures (a < b))
= Classical.move_requires (pow2_le_compat a) b

let lemma_mult_lt' (a: pos) (b c: int) : Lemma
  (requires (b < c))
  (ensures (a * b < a * c))
= ()

let lemma_mult_lt_recip  (a: pos) (b c: int) : Lemma
  (requires (a * b < a * c))
  (ensures (b < c))
= ()

let lemma_mult_le_recip (a: pos) (b c: int) : Lemma
  (requires (a * b <= a * c))
  (ensures (b <= c))
= ()

let le_antisym (x y: int) : Lemma
  (requires (x <= y /\ y <= x))
  (ensures (x == y))
= ()

let plus_minus_l (x y: int) : Lemma
  (x + y - x == y)
= ()

let plus_minus_r (x y: int) : Lemma
  (x + y - y == x)
= ()

let lemma_mult_nat (a b: nat) : Lemma
  (0 <= a * b)
= ()

inline_for_extraction
let mult_nat (a b: nat) : Tot (c: nat { c == a `Prims.op_Multiply` b } ) = a `Prims.op_Multiply` b
