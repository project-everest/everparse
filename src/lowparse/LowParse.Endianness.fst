module LowParse.Endianness

let rec index_be_to_n'
  (b: bytes)
  (i: nat)
: Lemma
  (requires (
    i < S.length b
  ))
  (ensures (
    U8.v (S.index b i) == (be_to_n b / pow2 (8 * (S.length b - 1 - i))) % pow2 8
  ))
  (decreases (S.length b))
= reveal_be_to_n b;
  if i = S.length b - 1
  then ()
  else begin
    let l = S.length b in
    let l' = l - 1 in
    let b' = S.slice b 0 l' in
    index_be_to_n' b' i;
    assert (S.index b i == S.index b' i);
    let open FStar.Math.Lemmas in
    let x = be_to_n b in
    let x' = be_to_n b' in
    assert (U8.v (S.index b i) == x' / pow2 (8 * (l' - 1 - i)) % pow2 8);
    let y = (U8.v (S.last b) + pow2 8 * x') / pow2 (8 * (l - 1 - i)) % pow2 8 in
    pow2_plus 8 (8 * (l' - 1 - i));
    division_multiplication_lemma (U8.v (S.last b) + pow2 8 * x') (pow2 8) (pow2 (8 * (l' - 1 - i)));
    assert (pow2 8 * x' == x' * pow2 8);
    division_addition_lemma (U8.v (S.last b)) (pow2 8) x';
    small_division_lemma_1 (U8.v (S.last b)) (pow2 8);
    assert (y == x' / pow2 (8 * (l' - 1 - i)) % pow2 8)
  end

let index_be_to_n = index_be_to_n'

let index_n_to_be
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    U8.v (S.index (n_to_be len n) i)) == (n / pow2 (8 * (len - 1 - i)) % pow2 8
  ))
= index_be_to_n (n_to_be len n) i

let index_n_to_be_zero_left
  (len: nat)
  (n: nat)
  (j: nat)
  (i: nat)
: Lemma
  (requires (
    i < j /\
    j <= len /\
    n < pow2 (8 * (len - j))
  ))
  (ensures (
    pow2 (8 * (len - j)) <= pow2 (8 * len) /\
    U8.v (S.index (n_to_be len n) i) == 0
  ))
= let open FStar.Math.Lemmas in
  pow2_le_compat (8 * len) (8 * (len - j));
  pow2_le_compat (8 * (len - 1 - i)) (8 * (len - j));
  small_division_lemma_1 n (pow2 (8 * (len - 1 - i)));
  index_n_to_be len n i

let index_n_to_be_zero_right
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len) /\
    n % pow2 (8 * (len - i)) == 0
  ))
  (ensures (
    U8.v (S.index (n_to_be len n) i) == 0
  ))
= index_n_to_be len n i;
  let open FStar.Math.Lemmas in
  modulo_division_lemma n (pow2 (8 * (len - 1 - i))) (pow2 8);
  pow2_plus (8 * (len - 1 - i)) 8
  
open FStar.Math.Lemmas

let rec be_to_n_append'
  (hi lo: bytes)
: Lemma
  (ensures (be_to_n (hi `S.append` lo) == be_to_n hi * pow2 (8 * S.length lo) + be_to_n lo))
  (decreases (S.length lo))
= reveal_be_to_n lo;
  let hilo = hi `S.append` lo in
  if S.length lo = 0
  then
    assert (hilo `S.equal` hi)
  else begin
    let lo' = S.slice lo 0 (S.length lo - 1) in
    assert (S.slice hilo 0 (S.length hilo - 1) `S.equal` (hi `S.append` lo'));
    assert (S.last hilo == S.last lo);
    reveal_be_to_n hilo;
    be_to_n_append' hi lo';
    pow2_plus (8 * S.length lo') 8
  end

let be_to_n_append = be_to_n_append'

let lemma_div_zero (x: pos) : Lemma
  (0 / x == 0)
= ()

let n_to_be_append
  (len: nat)
  (n: nat)
  (len_lo: nat)
: Lemma
  (requires (
    n < pow2 (8 * len) /\
    len_lo <= len
  ))
  (ensures (
    let hi = n / pow2 (8 * len_lo) in
    let lo = n % pow2 (8 * len_lo) in
    0 <= hi /\
    hi < pow2 (8 * (len - len_lo)) /\
    0 <= lo /\
    lo < pow2 (8 * len_lo) /\
    n_to_be len n == n_to_be (len - len_lo) hi `S.append` n_to_be len_lo lo
  ))
= lemma_div_zero (pow2 (8 * len_lo));
  lemma_div_le 0 n (pow2 (8 * len_lo));
  lemma_mod_lt n (pow2 (8 * len_lo));
  let hi = n / pow2 (8 * len_lo) in
  assert (0 <= hi);
  lemma_div_lt n (8 * len) (8 * len_lo);
  pow2_minus (8 * len) (8 * len_lo);
  let lo = n % pow2 (8 * len_lo) in
  euclidean_division_definition n (pow2 (8 * len_lo));
  let hi_s = n_to_be (len - len_lo) hi in
  let lo_s = n_to_be len_lo lo in
  be_to_n_append hi_s lo_s;
  assert (be_to_n (hi_s `S.append` lo_s) == n);
  be_to_n_inj (hi_s `S.append` lo_s) (n_to_be len n)

let reveal_n_to_be
  (len: nat)
  (n: nat)
: Lemma
  (requires (
    n < pow2 (8 * len)
  ))
  (ensures (
    (len > 0 ==> (0 <= n / pow2 8 /\ n / pow2 8 < pow2 (8 * (len - 1)))) /\
    n_to_be len n `S.equal` (if len = 0 then S.empty else n_to_be (len - 1) (n / pow2 8) `S.snoc` (U8.uint_to_t (n % pow2 8)))
  ))
= if len = 0
  then ()
  else begin
    n_to_be_append len n 1;
    index_n_to_be 1 (n % pow2 8) 0
  end

let slice_n_to_be
  (len: nat)
  (n: nat)
  (i j: nat)
: Lemma
  (requires (
    i <= j /\
    j <= len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    let res = (n / pow2 (8 * (len - j))) % pow2 (8 * (j - i)) in
    0 <= res /\
    res < pow2 (8 * (j - i)) /\
    S.slice (n_to_be len n) i j == n_to_be (j - i) res
  ))
= let s1 = S.slice (n_to_be len n) 0 j in
  let s2 = S.slice s1 i j in
  n_to_be_append len n (len - j);
  let q = n / pow2 (8 * (len - j)) in
  n_to_be_append j q (j - i);
  let r = q % pow2 (8 * (j - i)) in
  assert (s2 `S.equal` n_to_be (j - i) (q % pow2 (8 * (j - i))))

let rec seq_rev
  (#t: Type)
  (x: S.seq t)
: Tot (y: S.seq t {S.length y == S.length x})
  (decreases (S.length x))
= if S.length x = 0
  then S.empty
  else seq_rev (S.tail x) `S.append` S.create 1 (S.head x)

let rec index_seq_rev'
  (#t: Type)
  (x: S.seq t)
  (i: nat {i < S.length x})
: Lemma
  (ensures (S.index (seq_rev x) (S.length x - 1 - i) == S.index x i))
  (decreases (S.length x))
= if i = 0
  then
    S.lemma_index_create 1 (S.head x) 0
  else
    index_seq_rev' (S.tail x) (i - 1)

let index_seq_rev
  (#t: Type)
  (x: S.seq t)
  (i: nat {i < S.length x})
: Lemma
  (ensures (S.index (seq_rev x) i == S.index x (S.length x - 1 - i)))
= index_seq_rev' x (S.length x - 1 - i)

let slice_seq_rev
  (#t: Type)
  (x: S.seq t)
  (i: nat)
  (j: nat)
: Lemma
  (requires (i <= j /\ j <= S.length x))
  (ensures (S.slice (seq_rev x) i j `S.equal` seq_rev (S.slice x (S.length x - j) (S.length x - i))))
= Classical.forall_intro (index_seq_rev x);
  Classical.forall_intro (index_seq_rev (S.slice x (S.length x - j) (S.length x - i)))

let rec le_to_n_eq_be_to_n_rev
  (b: bytes)
: Lemma
  (ensures (le_to_n b == be_to_n (seq_rev b)))
  (decreases (S.length b))
= reveal_be_to_n (seq_rev b);
  reveal_le_to_n b;
  if Seq.length b = 0
  then ()
  else begin
    index_seq_rev b (S.length b - 1);
    slice_seq_rev b 0 (S.length b - 1);
    le_to_n_eq_be_to_n_rev (S.tail b)
  end

let seq_rev_involutive
  (#t: Type)
  (x: S.seq t)
: Lemma
  (seq_rev (seq_rev x) `S.equal` x)
= Classical.forall_intro (index_seq_rev (seq_rev x));
  Classical.forall_intro (index_seq_rev x)

let n_to_le_eq_rev_n_to_be
  (len: nat)
  (n: nat)
: Lemma
  (requires (n < pow2 (8 * len)))
  (ensures (n_to_le len n == seq_rev (n_to_be len n)))
= le_to_n_eq_be_to_n_rev (n_to_le len n);
  be_to_n_inj (seq_rev (n_to_le len n)) (n_to_be len n);
  seq_rev_involutive (n_to_le len n)

let index_le_to_n
  b i
= le_to_n_eq_be_to_n_rev b;
  index_be_to_n (seq_rev b) (S.length b - 1 - i);
  index_seq_rev b (S.length b - 1 - i)

let index_n_to_le
  len n i
= n_to_le_eq_rev_n_to_be len n;
  index_seq_rev (n_to_be len n) i;
  index_n_to_be len n (len - 1 - i)

let seq_rev_append
  (#t: Type)
  (b1 b2: S.seq t)
: Lemma
  (seq_rev (b1 `S.append` b2) `S.equal` (seq_rev b2 `S.append` seq_rev b1))
= Classical.forall_intro (index_seq_rev (b1 `S.append` b2));
  Classical.forall_intro (index_seq_rev b1);
  Classical.forall_intro (index_seq_rev b2)

let n_to_le_append
  (len: nat)
  (n: nat)
  (len_lo: nat)
: Lemma
  (requires (
    n < pow2 (8 * len) /\
    len_lo <= len
  ))
  (ensures (
    let hi = n / pow2 (8 * len_lo) in
    let lo = n % pow2 (8 * len_lo) in
    0 <= hi /\
    hi < pow2 (8 * (len - len_lo)) /\
    0 <= lo /\
    lo < pow2 (8 * len_lo) /\
    n_to_le len n == n_to_le len_lo lo `S.append` n_to_le (len - len_lo) hi
  ))
=
  let hi = n / pow2 (8 * len_lo) in
  let lo = n % pow2 (8 * len_lo) in
  n_to_be_append len n len_lo;
  n_to_le_eq_rev_n_to_be len n;
  n_to_le_eq_rev_n_to_be len_lo lo;
  n_to_le_eq_rev_n_to_be (len - len_lo) hi;
  seq_rev_append (n_to_be (len - len_lo) hi) (n_to_be len_lo lo)

let reveal_n_to_le
  (len: nat)
  (n: nat)
: Lemma
  (requires (
    n < pow2 (8 * len)
  ))
  (ensures (
    (len > 0 ==> (0 <= n / pow2 8 /\ n / pow2 8 < pow2 (8 * (len - 1)))) /\
    n_to_le len n `S.equal` (if len = 0 then S.empty else (U8.uint_to_t (n % pow2 8) `S.cons` n_to_le (len - 1) (n / pow2 8)))
  ))
= if len = 0
  then ()
  else begin
    n_to_le_append len n 1;
    index_n_to_le 1 (n % pow2 8) 0
  end
