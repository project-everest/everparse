module ASN1.Spec.Content.INTEGER

module BF = LowParse.BitFields
module E = LowParse.Endianness.BitFields
module U = FStar.UInt
module U8 = FStar.UInt8

open FStar.Mul

// Make all integer proofs (pow2, etc.) explicit
#push-options "--z3cliopt smt.arith.nl=false --fuel 0"

let rec be_to_n_leading_zeros
  (s: Seq.seq U8.t)
: Lemma
  (requires (Seq.length s > 0))
  (ensures (
    E.be_to_n s < pow2 (8 * (Seq.length s - 1)) <==> U8.v (Seq.index s 0) == 0
  ))
  (decreases (Seq.length s))
= E.reveal_be_to_n s;
  let unfold s' = Seq.slice s 0 (Seq.length s - 1) in
  E.reveal_be_to_n s';
  assert_norm (pow2 0 == 1);
  assert_norm (pow2 8 == 256);
  if Seq.length s = 1
  then ()
  else begin
    be_to_n_leading_zeros s';
    FStar.Math.Lemmas.pow2_plus 8 (8 * (Seq.length s' - 1))
  end

let rec be_to_n_chop_leading_zeros
  (s: Seq.seq U8.t)
: Lemma
  (requires (
    Seq.length s > 0 /\
    U8.v (Seq.index s 0) == 0
  ))
  (ensures (
    E.be_to_n s == E.be_to_n (Seq.slice s 1 (Seq.length s))
  ))
  (decreases (Seq.length s))
=
  E.reveal_be_to_n s;
  let s' = Seq.slice s 0 (Seq.length s - 1) in
  E.reveal_be_to_n s';
  let sm = Seq.slice s 1 (Seq.length s) in
  E.reveal_be_to_n sm;
  assert_norm (pow2 8 == 256);
  if Seq.length s = 1
  then ()
  else begin
    be_to_n_chop_leading_zeros s';
    FStar.Math.Lemmas.pow2_plus 8 (8 * (Seq.length s' - 1))
  end

let rec be_to_n_chop_leading_zeros_seq
  (s: Seq.seq U8.t)
  (d: nat)
: Lemma
  (requires (
    True
  ))
  (ensures (
    E.be_to_n (Seq.create d 0uy `Seq.append` s)  == E.be_to_n s
  ))
  (decreases d)
= let s' = Seq.create d 0uy `Seq.append` s in
  if d = 0
  then assert (s' `Seq.equal` s)
  else begin
    let s1 = Seq.cons 0uy s in
    be_to_n_chop_leading_zeros s1;
    assert (Seq.slice s1 1 (Seq.length s1) `Seq.equal` s);
    be_to_n_chop_leading_zeros_seq s1 (d - 1);
    assert (s' `Seq.equal` (Seq.create (d - 1) 0uy `Seq.append` s1))
  end

let be_to_n_chop_leading_zeros_recip
  (s1 s2: Seq.seq U8.t)
: Lemma
  (requires (
    Seq.length s1 > 0 /\
    Seq.length s1 <= Seq.length s2 /\
    E.be_to_n s1 == E.be_to_n s2
  ))
  (ensures (
    s2 `Seq.equal` (Seq.create (Seq.length s2 - Seq.length s1) 0uy `Seq.append` s1)
  ))
= let d = Seq.length s2 - Seq.length s1 in
  let s2' = Seq.create d 0uy `Seq.append` s1 in
  be_to_n_chop_leading_zeros_seq s1 d;
  E.be_to_n_inj s2' s2

let rec be_to_n_msb
  (s: Seq.seq U8.t)
: Lemma
  (requires (Seq.length s > 0))
  (ensures (
    E.be_to_n s >= pow2 (8 * Seq.length s - 1) <==> U8.v (Seq.index s 0) >= 128
  ))
  (decreases (Seq.length s))
= E.reveal_be_to_n s;
  let s' = Seq.slice s 0 (Seq.length s - 1) in
  E.reveal_be_to_n s';
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  if Seq.length s = 1
  then ()
  else begin
    be_to_n_msb s';
    FStar.Math.Lemmas.pow2_plus 8 (8 * Seq.length s' - 1)
  end

let outer_positive_interval (n: nat) (x: int) : Tot prop =
  n > 0 /\
  x >= pow2 (8 * (n - 1)) /\
  x < pow2 (8 * n - 1)

let outer_positive_interval_intro (x: Seq.seq U8.t) : Lemma
  (requires (
    Seq.length x > 0 /\
    begin let c = U8.v (Seq.index x 0) in
    c > 0 /\ c < 128
    end
  ))
  (ensures (
    outer_positive_interval (Seq.length x) (E.be_to_n x)
  ))
= be_to_n_leading_zeros x;
  be_to_n_msb x

let outer_positive_interval_elim (n: nat) (x: int) : Lemma
  (requires (
    outer_positive_interval n x
  ))
  (ensures (
    x > 0 /\ x < pow2 (8 * n) /\
    begin let c = U8.v (Seq.index (E.n_to_be n x) 0) in
    c > 0 /\ c < 128
    end    
  ))
= FStar.Math.Lemmas.pow2_le_compat (8 * n) (8 * n - 1);
  let s = E.n_to_be n x in
  be_to_n_leading_zeros s;
  be_to_n_msb s

let inner_positive_interval (n: nat) (x: int) : Tot prop =
  n > 1 /\
  x >= pow2 (8 * (n - 1) - 1) /\
  x < pow2 (8 * (n - 1))

let inner_positive_interval_intro (x: Seq.seq U8.t) : Lemma
  (requires (
    Seq.length x > 1 /\
    U8.v (Seq.index x 0) == 0 /\
    U8.v (Seq.index x 1) >= 128
  ))
  (ensures (
    inner_positive_interval (Seq.length x) (E.be_to_n x)
  ))
= be_to_n_leading_zeros x;
  be_to_n_chop_leading_zeros x;
  be_to_n_msb (Seq.slice x 1 (Seq.length x))

let inner_positive_interval_elim (n: nat) (x: int) : Lemma
  (requires (inner_positive_interval n x))
  (ensures (
    x > 0 /\ x < pow2 (8 * n) /\
    begin let s = E.n_to_be n x in
    Seq.length s > 1 /\
    U8.v (Seq.index s 0) == 0 /\
    U8.v (Seq.index s 1) >= 128
    end
  ))
= FStar.Math.Lemmas.pow2_lt_compat (8 * n) (8 * (n - 1));
  let s = E.n_to_be n x in
  be_to_n_leading_zeros s;
  be_to_n_chop_leading_zeros s;
  be_to_n_msb (Seq.slice s 1 (Seq.length s))

let rec be_to_n_leading_ones
  (s: Seq.seq U8.t)
: Lemma
  (requires (Seq.length s > 0))
  (ensures (
    E.be_to_n s >= pow2 (8 * (Seq.length s - 1)) * 255 <==> U8.v (Seq.index s 0) == 255
  ))
  (decreases (Seq.length s))
= E.reveal_be_to_n s;
  let s' = Seq.slice s 0 (Seq.length s - 1) in
  E.reveal_be_to_n s';
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  if Seq.length s = 1
  then ()
  else begin
    be_to_n_leading_ones s';
    FStar.Math.Lemmas.pow2_plus 8 (8 * (Seq.length s' - 1))
  end

let pow2_8_n_255 (n: nat) : Lemma
  (pow2 (8 * n) * 255 == pow2 (8 * (n + 1)) - pow2 (8 * n))
= assert_norm (pow2 8 == 256);
  FStar.Math.Lemmas.pow2_plus (8 * n) 8

// 2's complement representation of negative integers can have their leading ones chopped

let rec be_to_n_chop_leading_ones
  (s: Seq.seq U8.t)
: Lemma
  (requires (
    Seq.length s > 0 /\
    U8.v (Seq.index s 0) == 255
  ))
  (ensures (
    E.be_to_n s - pow2 (8 * Seq.length s) == E.be_to_n (Seq.slice s 1 (Seq.length s)) - pow2 (8 * (Seq.length s - 1))
  ))
  (decreases (Seq.length s))
= E.reveal_be_to_n s;
  let s' = Seq.slice s 0 (Seq.length s - 1) in
  E.reveal_be_to_n s';
  let sm = Seq.slice s 1 (Seq.length s) in
  E.reveal_be_to_n sm;
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  if Seq.length s = 1
  then ()
  else begin
    be_to_n_chop_leading_ones s';
    FStar.Math.Lemmas.pow2_plus 8 (8 * (Seq.length s - 1));
    FStar.Math.Lemmas.pow2_plus 8 (8 * (Seq.length s' - 1))
  end

let rec be_to_n_chop_leading_ones_seq
  (s: Seq.seq U8.t)
  (d: nat)
: Lemma
  (requires (
    True
  ))
  (ensures (
    let s' = Seq.create d 255uy `Seq.append` s in
    E.be_to_n s' - pow2 (8 * Seq.length s') == E.be_to_n s - pow2 (8 * Seq.length s)
  ))
  (decreases d)
= let s' = Seq.create d 255uy `Seq.append` s in
  if d = 0
  then assert (s' `Seq.equal` s)
  else begin
    let s1 = Seq.cons 255uy s in
    be_to_n_chop_leading_ones s1;
    assert (Seq.slice s1 1 (Seq.length s1) `Seq.equal` s);
    be_to_n_chop_leading_ones_seq s1 (d - 1);
    assert (s' `Seq.equal` (Seq.create (d - 1) 255uy `Seq.append` s1))
  end

let be_to_n_chop_leading_ones_recip
  (s1 s2: Seq.seq U8.t)
: Lemma
  (requires (
    Seq.length s1 <= Seq.length s2 /\
    E.be_to_n s1 - pow2 (8 * Seq.length s1) == E.be_to_n s2 - pow2 (8 * Seq.length s2)
  ))
  (ensures (
    s2 `Seq.equal` (Seq.create (Seq.length s2 - Seq.length s1) 255uy `Seq.append` s1)
  ))
= let d = Seq.length s2 - Seq.length s1 in
  let s2' = Seq.create d 255uy `Seq.append` s1 in
  be_to_n_chop_leading_ones_seq s1 d;
  E.be_to_n_inj s2' s2

let outer_negative_interval (n: nat) (x: int) : Tot prop =
  n > 0 /\
  begin let u = x + pow2 (8 * n) in
  u < pow2 (8 * (n - 1)) * 255 /\
  u >= pow2 (8 * n - 1)
  end

let outer_negative_interval_intro (x: Seq.seq U8.t) : Lemma
  (requires (
    Seq.length x > 0 /\
    begin let c = U8.v (Seq.index x 0) in
    c >= 128 /\ c < 255
    end
  ))
  (ensures (
    outer_negative_interval (Seq.length x) (E.be_to_n x - pow2 (8 * Seq.length x))
  ))
= be_to_n_msb x;
  be_to_n_leading_ones x

let outer_negative_interval_elim (n: nat) (x: int) : Lemma
  (requires (
    outer_negative_interval n x
  ))
  (ensures (
    n > 0 /\
    begin let u = x + pow2 (8 * n) in
    0 <= u /\
    u < pow2 (8 * n) /\
    x < -1 /\
    begin let c = U8.v (Seq.index (E.n_to_be n u) 0) in
    c >= 128 /\ c < 255
    end end
  ))
= let u = x + pow2 (8 * n) in
  assert_norm (256 == pow2 8);
  FStar.Math.Lemmas.pow2_plus (8 * (n - 1)) 8;
  let s = E.n_to_be n u in
  be_to_n_msb s;
  be_to_n_leading_ones s

let inner_negative_interval (n: nat) (x: int) : Tot prop =
  n > 1 /\
  x + pow2 (8 * n) >= pow2 (8 * (n - 1)) * 255 /\
  x + pow2 (8 * (n - 1)) < pow2 (8 * (n - 1) - 1)

let inner_negative_interval_upper_bound (n: nat) (x: int) : Lemma
  (requires (inner_negative_interval n x))
  (ensures (
    0 <= x + pow2 (8 * n) /\
    x + pow2 (8 * n) < pow2 (8 * n)
  ))
= FStar.Math.Lemmas.pow2_plus (8 * (n - 1) - 1) 1

let inner_negative_interval_intro (x: Seq.seq U8.t) : Lemma
  (requires (
    Seq.length x > 1 /\
    U8.v (Seq.index x 0) == 255 /\
    begin let c = U8.v (Seq.index x 1) in
    c < 128
    end
  ))
  (ensures (
    inner_negative_interval (Seq.length x) (E.be_to_n x - pow2 (8 * Seq.length x))
  ))
= be_to_n_leading_ones x;
  be_to_n_chop_leading_ones x;
  be_to_n_msb (Seq.slice x 1 (Seq.length x))

let inner_negative_interval_elim (n: nat) (x: int) : Lemma
  (requires (
    inner_negative_interval n x
  ))
  (ensures (
    n > 1 /\
    x < -1 /\
    begin let u = x + pow2 (8 * n) in
    let u' = x + pow2 (8 * (n - 1)) in
    0 <= u /\ u < pow2 (8 * n) /\
    0 <= u' /\ u' < pow2 (8 * (n - 1)) /\
    begin let s = E.n_to_be n u in
    let s' = E.n_to_be (n - 1) u' in
    U8.v (Seq.index s 0) == 255 /\
    s' `Seq.equal` Seq.slice s 1 (Seq.length s) /\
    begin let c = U8.v (Seq.index s 1) in
    c < 128
    end end end
  ))
= let u' = x + pow2 (8 * (n - 1)) in
  pow2_8_n_255 (n - 1);
  FStar.Math.Lemmas.pow2_le_compat (8 * (n - 1)) (8 * (n - 1) - 1);
  let s' = E.n_to_be (n - 1) u' in
  let s = Seq.cons 255uy s' in
  assert (Seq.slice s 1 (Seq.length s) `Seq.equal` s');
  be_to_n_leading_ones s;
  be_to_n_chop_leading_ones s;
  be_to_n_msb s';
  FStar.Math.Lemmas.pow2_lt_compat (8 * (n - 1)) (8 * (n - 1) - 1)

(* Sanity-check: the whole signed interval is covered *)

let domain (n: nat) (x: int) : Tot prop =
  (n == 1 /\ (x == 0 \/ x == -1)) \/ inner_positive_interval n x \/ outer_positive_interval n x \/ inner_negative_interval n x \/ outer_negative_interval n x

let interval (n: nat) (x: int) : Tot prop =
  n > 0 /\
  begin let abs_val = pow2 (8 * n - 1) in
  0 - abs_val <= x /\ x < abs_val
  end

let interval_weaken (n1 n2: nat) (x: int) : Lemma
  (requires (interval n1 x /\ n1 <= n2))
  (ensures (interval n2 x))
= FStar.Math.Lemmas.pow2_le_compat (8 * n2 - 1) (8 * n1 - 1)

let interval_intro_inner_positive (n: nat) (x: int) : Lemma
  (requires (inner_positive_interval n x))
  (ensures (interval n x))
= FStar.Math.Lemmas.pow2_le_compat (8 * n - 1) (8 * (n - 1))

let interval_intro_outer_positive (n: nat) (x: int) : Lemma
  (requires (outer_positive_interval n x))
  (ensures (interval n x))
= ()

let interval_intro_inner_negative (n: nat) (x: int) : Lemma
  (requires (inner_negative_interval n x))
  (ensures (interval n x))
= inner_negative_interval_elim n x;
  FStar.Math.Lemmas.pow2_le_compat (8 * n - 1) (8 * (n - 1))
  
let interval_intro_outer_negative (n: nat) (x: int) : Lemma
  (requires (outer_negative_interval n x))
  (ensures (interval n x))
= assert_norm (pow2 1 == 2);
  FStar.Math.Lemmas.pow2_plus (8 * n - 1) 1;
  outer_negative_interval_elim n x

let interval_intro (n: nat) (x: int) : Lemma
  (requires (domain n x))
  (ensures (interval n x))
= Classical.move_requires (interval_intro_inner_negative n) x;
  Classical.move_requires (interval_intro_inner_positive n) x;
  Classical.move_requires (interval_intro_outer_negative n) x;
  Classical.move_requires (interval_intro_outer_positive n) x

let rec interval_elim (n: nat) (x: int) : Pure nat
  (requires (
    interval n x
  ))
  (ensures (fun n' ->
    n' <= n /\ domain n' x
  ))
  (decreases n)
= if x = 0 || x = -1
  then 1
  else if x > 0
  then begin
    FStar.Math.Lemmas.pow2_le_compat (8 * n) (8 * n - 1);
    let s = E.n_to_be n x in
    let c0 = U8.v (Seq.index s 0) in
    be_to_n_msb s;
    if c0 > 0
    then begin
      outer_positive_interval_intro s;
      n
    end else begin
      be_to_n_chop_leading_zeros s;
      let s' = Seq.slice s 1 (Seq.length s) in
      if n = 1
      then begin
        E.reveal_be_to_n s';
        assert False;
        n
      end else begin
        assert (n > 1);
        be_to_n_msb s';
        if U8.v (Seq.index s 1) >= 128
        then begin
          inner_positive_interval_intro s;
          n
        end else begin
          interval_elim (n - 1) x
        end
      end
    end
  end else begin
    let u = x + pow2 (8 * n) in
    FStar.Math.Lemmas.pow2_plus (8 * n - 1) 1;
    assert_norm (pow2 1 == 2);
    let s = E.n_to_be n u in
    be_to_n_msb s;
    be_to_n_leading_ones s;
    if U8.v (Seq.index s 0) < 255
    then begin
      outer_negative_interval_intro s;
      n
    end else begin
      be_to_n_chop_leading_ones s;
      let s' = Seq.slice s 1 (Seq.length s) in
      if n = 1
      then begin
        E.reveal_be_to_n s';
        assert False;
        n
      end else begin
        assert (n > 1);
        let u' = x + pow2 (8 * (n - 1)) in
        assert (s' == E.n_to_be (n - 1) u');
        let c1 = U8.v (Seq.index s' 0) in
        be_to_n_msb s';
        if c1 < 128
        then begin
          inner_negative_interval_intro s;
          n
        end else begin
          FStar.Math.Lemmas.pow2_plus (8 * (n - 1) - 1) 1;
          interval_elim (n - 1) x
        end
      end
    end
  end

let interval_equiv (n: nat) (x: int) : Lemma
  (interval n x <==> (exists (n': nat) . n' <= n /\ domain n' x))
=
  let f () : Lemma
    (requires (interval n x))
    (ensures (exists (n': nat) . n' <= n /\ domain n' x))
  = let _ = interval_elim n x in
    ()
  in
  let g
    (n': nat)
  : Lemma
    (requires (n' <= n /\ domain n' x))
    (ensures (interval n x))
  = interval_intro n' x;
    interval_weaken n' n x
  in
  Classical.move_requires f ();
  Classical.forall_intro (Classical.move_requires g)

let rec some_log256
  (x: nat)
: Pure nat
  (requires True)
  (ensures (fun n -> n > 0 /\ x < pow2 (8 * n)))
  (decreases x)
= assert_norm (pow2 8 == 256);
  if x < 256
  then 1
  else begin
    FStar.Math.Lemmas.euclidean_division_definition x 256;
    let n' = some_log256 (x / 256) in
    FStar.Math.Lemmas.pow2_plus (8 * n') 8;
    n' + 1
  end

let interval_intro_gen
  (x: int)
: Pure nat
  (requires True)
  (ensures (fun n -> n > 0 /\ interval n x))
= if x >= 0
  then begin
    let n = some_log256 x in
    FStar.Math.Lemmas.pow2_le_compat (8 * (n + 1) - 1) (8 * n);
    n + 1
  end
  else begin
    let n = some_log256 (- x) in
    FStar.Math.Lemmas.pow2_le_compat (8 * (n + 1) - 1) (8 * n);
    n + 1
  end

let domain_intro_gen
  (x: int)
: Pure nat
  (requires True)
  (ensures (fun n -> domain n x))
= let n' = interval_intro_gen x in
  interval_elim n' x

(* Correctness: the representation is minimal *)

let positive_interval_minimal
  (n: nat)
  (x: int)
  (n': nat)
: Lemma
  (requires (
    domain n x /\
    x >= 0 /\
    n' > 0 /\
    x < pow2 (8 * n') /\
    U8.v (Seq.index (E.n_to_be n' x) 0) < 128
  ))
  (ensures (n <= n'))
= Classical.move_requires (inner_positive_interval_elim n) x;
  Classical.move_requires (outer_positive_interval_elim n) x;
  Classical.move_requires (inner_negative_interval_elim n) x;
  Classical.move_requires (outer_negative_interval_elim n) x;
  if x = 0
  then assert (n == 1)
  else if n <= n'
  then ()
  else begin
    interval_intro n x;
    FStar.Math.Lemmas.pow2_le_compat (8 * n) (8 * n - 1);
    be_to_n_chop_leading_zeros_recip (E.n_to_be n' x) (E.n_to_be n x)
  end

let positive_interval_minimal'
  (n: nat)
  (x: int)
  (n': nat)
: Lemma
  (requires (
    domain n x /\
    x >= 0 /\
    n' > 0 /\
    x < pow2 (8 * n' - 1)
  ))
  (ensures (
    x < pow2 (8 * n') /\
    U8.v (Seq.index (E.n_to_be n' x) 0) < 128 /\
    n <= n'
  ))
= FStar.Math.Lemmas.pow2_le_compat (8 * n') (8 * n' - 1);
  be_to_n_msb (E.n_to_be n' x);
  positive_interval_minimal n x n'

let negative_interval_minimal
  (n: nat)
  (x: int)
  (n': nat)
: Lemma
  (requires (
    domain n x /\
    x < 0 /\
    n' > 0 /\
    x + pow2 (8 * n') >= 0 /\
    U8.v (Seq.index (E.n_to_be n' (x + pow2 (8 * n'))) 0) >= 128
  ))
  (ensures (
    n <= n'
  ))
= Classical.move_requires (inner_positive_interval_elim n) x;
  Classical.move_requires (outer_positive_interval_elim n) x;
  Classical.move_requires (inner_negative_interval_elim n) x;
  Classical.move_requires (outer_negative_interval_elim n) x;
  if x = -1
  then assert (n == 1)
  else if n <= n'
  then ()
  else begin
    interval_intro n x;
    FStar.Math.Lemmas.pow2_le_compat (8 * n) (8 * n - 1);
    be_to_n_chop_leading_ones_recip (E.n_to_be n' (x + pow2 (8 * n'))) (E.n_to_be n (x + pow2 (8 * n)))
  end

let negative_interval_minimal'
  (n: nat)
  (x: int)
  (n': nat)
: Lemma
  (requires (
    domain n x /\
    x < 0 /\
    n' > 0 /\
    x + pow2 (8 * n' - 1) >= 0
  ))
  (ensures (
    x + pow2 (8 * n') >= 0 /\
    U8.v (Seq.index (E.n_to_be n' (x + pow2 (8 * n'))) 0) >= 128 /\
    n <= n'
  ))
= FStar.Math.Lemmas.pow2_le_compat (8 * n') (8 * n' - 1);
  FStar.Math.Lemmas.pow2_plus (8 * n' - 1) 1;
  assert_norm (pow2 1 == 2);
  be_to_n_msb (E.n_to_be n' (x + pow2 (8 * n')));
  negative_interval_minimal n x n'

let domain_unique'
  (n1 n2: nat)
  (x: int)
: Lemma
  (requires (n1 <= n2 /\ domain n1 x /\ domain n2 x))
  (ensures (n1 == n2))
= interval_intro n1 x;
  if x < 0
  then negative_interval_minimal' n2 x n1
  else positive_interval_minimal' n2 x n1

let domain_unique
  (n1 n2: nat)
  (x: int)
: Lemma
  (requires (domain n1 x /\ domain n2 x))
  (ensures (n1 == n2))
= if n1 <= n2
  then domain_unique' n1 n2 x
  else domain_unique' n2 n1 x

(* Parser *)

module LP = LowParse.Tot.Combinators

let valid_unsigned_repr
  (b: LP.bytes)
: Tot bool
= let n = Seq.length b in
  n > 0 &&
  begin if n = 1
  then true
  else
    let c0 = Seq.index b 0 in
    let c1 = Seq.index b 1 in
    not ((c0 = 0uy && c1 `U8.lt` 128uy) || (c0 = 255uy && 127uy `U8.lt` c1))
  end

let integer_in_domain (n: nat) : Tot Type0 = (i: int { domain n i })

let rec be_to_n_zero
  (n: nat)
: Lemma
  (E.be_to_n (Seq.create n 0uy) == 0)
= let unfold s = Seq.create n 0uy in
  E.reveal_be_to_n s;
  assert (Seq.length s == n);
  if n = 0
  then ()
  else begin
    assert (Seq.slice s 0 (Seq.length s - 1) `Seq.equal` Seq.create (n - 1) 0uy);
    be_to_n_zero (n - 1)
  end

let be_to_n_singleton
  (s: LP.bytes)
: Lemma
  (requires (
    Seq.length s == 1
  ))
  (ensures (
    Seq.length s == 1 /\
    E.be_to_n s == U8.v (Seq.index s 0)
  ))
= E.reveal_be_to_n s;
  E.reveal_be_to_n (Seq.slice s 0 (Seq.length s - 1))

let mk_integer_aux
  (b: LP.bytes)
: Tot (option (integer_in_domain (Seq.length b)))
= if valid_unsigned_repr b
  then Some begin
    let u = E.be_to_n b in
    let c0 = Seq.index b 0 in
    if c0 = 0uy
    then
      if Seq.length b = 1
      then begin
        be_to_n_singleton b;
        u
      end
      else begin
        inner_positive_interval_intro b;
        u
      end
    else if c0 `U8.lt` 128uy
    then begin
      outer_positive_interval_intro b;
      u
    end
    else
      let s = u - pow2 (8 * Seq.length b) in // cast from unsigned to signed for negative numbers
      if c0 `U8.lt` 255uy
      then begin
        outer_negative_interval_intro b;
        s
      end
      else if Seq.length b = 1
      then begin
        be_to_n_singleton b;
        assert_norm (pow2 8 == 256);
        assert (s == -1);
        s
      end
      else begin
        inner_negative_interval_intro b;
        s
      end
  end else None

let mk_integer'_eq'
  (b: LP.bytes)
: Lemma
  (requires (valid_unsigned_repr b))
  (ensures (
    let u = E.be_to_n b in
    let s = Some?.v (mk_integer_aux b) in
    (s >= 0 <==> s == u) /\
    (s < 0 <==> s == u - pow2 (8 * Seq.length b))
  ))
= let n = Seq.length b in
  let u = E.be_to_n b in
  let s = Some?.v (mk_integer_aux b) in
  FStar.Math.Lemmas.pow2_plus (8 * n - 1) 1;
  Classical.move_requires inner_positive_interval_intro b;
  Classical.move_requires outer_positive_interval_intro b; 
  Classical.move_requires inner_negative_interval_intro b;
  Classical.move_requires outer_negative_interval_intro b; 
  Classical.move_requires (inner_positive_interval_elim n) s;
  Classical.move_requires (outer_positive_interval_elim n) s;
  Classical.move_requires (inner_negative_interval_elim n) s;
  Classical.move_requires (outer_negative_interval_elim n) s;
  Classical.move_requires be_to_n_singleton b

let mk_integer'_eq
  (b: LP.bytes)
: Lemma
  (requires (valid_unsigned_repr b))
  (ensures (
    let u = E.be_to_n b in
    let s = Some?.v (mk_integer_aux b) in
    (s >= 0 <==> u < pow2 (8 * Seq.length b - 1)) /\
    (s >= 0 <==> s == u) /\
    (s < 0 <==> s == u - pow2 (8 * Seq.length b))
  ))
= let n = Seq.length b in
  let u = E.be_to_n b in
  let s = Some?.v (mk_integer_aux b) in
  mk_integer'_eq' b;
  interval_intro n s;
  FStar.Math.Lemmas.pow2_plus (8 * n - 1) 1

let mk_integer'
  (b: LP.bytes)
: Pure int
  (requires (valid_unsigned_repr b))
  (ensures (fun _ -> True))
= let u = E.be_to_n b in
  if u < pow2 (8 * Seq.length b - 1)
  then u
  else u - pow2 (8 * Seq.length b)

let mk_integer
  (sz: nat)
  (b: LP.bytes { Seq.length b == sz })
: Tot (option (integer_in_domain sz))
= if valid_unsigned_repr b
  then Some (
    mk_integer'_eq b;
    mk_integer' b
  )
  else None

let mk_integer_inj_1
  (sz: nat)
  (b1 b2: Seq.lseq LP.byte sz)
: Lemma
  (requires (LP.make_constant_size_parser_precond_precond sz (integer_in_domain sz) (mk_integer sz) b1 b2))
  (ensures (Seq.equal b1 b2))
= mk_integer'_eq b1;
  mk_integer'_eq b2;
  E.be_to_n_inj b1 b2

let mk_integer_inj_2
  (sz: nat)
  (b1 b2: Seq.lseq LP.byte sz)
: Lemma
  (LP.make_constant_size_parser_precond_precond sz (integer_in_domain sz) (mk_integer sz) b1 b2 ==> Seq.equal b1 b2)
= Classical.move_requires (mk_integer_inj_1 sz b1) b2

let mk_integer_inj
  (sz: nat)
: Lemma
  (LP.make_constant_size_parser_precond sz (integer_in_domain sz) (mk_integer sz))
= Classical.forall_intro_2 (mk_integer_inj_2 sz)

let parse_integer_of_size
  (sz: nat)
: Tot (LP.parser (LP.constant_size_parser_kind sz) (integer_in_domain sz))
= mk_integer_inj sz;
  LP.make_constant_size_parser sz (integer_in_domain sz) (mk_integer sz)

let bounded_integer_tag
  (bound: nat)
: Tot Type0
= (sz: nat { sz <= bound })

let integer_in_interval
  (bound: nat)
: Tot Type0
= (x: int { interval bound x })

let tag_of_bounded_integer_payload
  (bound: nat)
  (x: integer_in_interval bound)
: Tot (bounded_integer_tag bound)
= interval_elim bound x

let synth_bounded_integer_payload
  (bound: nat)
  (tag: bounded_integer_tag bound)
  (x: integer_in_domain tag)
: Tot (LP.refine_with_tag (tag_of_bounded_integer_payload bound) tag)
= interval_intro tag x;
  interval_weaken tag bound x;
  domain_unique tag (tag_of_bounded_integer_payload bound x) x;
  x

let parse_bounded_integer_payload
  (bound: nat)
  (tag: bounded_integer_tag bound)
: Tot (LP.parser (LP.strong_parser_kind 0 bound None) (LP.refine_with_tag (tag_of_bounded_integer_payload bound) tag))
= LP.weaken (LP.strong_parser_kind 0 bound None) (parse_integer_of_size tag)
  `LP.parse_synth` synth_bounded_integer_payload bound tag

let parse_bounded_integer
  (bound: nat)
  (#kt: LP.parser_kind)
  (p: LP.parser kt (bounded_integer_tag bound) {
    kt.LP.parser_kind_subkind == Some LP.ParserStrong
  })
: Tot (LP.parser (kt `LP.and_then_kind` LP.strong_parser_kind 0 bound None) (integer_in_interval bound))
= LP.parse_tagged_union
    p
    (tag_of_bounded_integer_payload bound)
    (parse_bounded_integer_payload bound)

let mk_integer'_inj'
  (b1 b2: LP.bytes)
: Lemma
  (requires (valid_unsigned_repr b1 /\ valid_unsigned_repr b2 /\ mk_integer' b1 == mk_integer' b2))
  (ensures (b1 == b2))
= mk_integer'_eq' b1;
  mk_integer'_eq' b2;
  let n = mk_integer' b1 in
  domain_unique (Seq.length b1) (Seq.length b2) n;
  mk_integer_inj_1 (Seq.length b1) b1 b2

let mk_integer'_inj
  (b1 b2: LP.bytes)
: Lemma
  ((valid_unsigned_repr b1 /\ valid_unsigned_repr b2 /\ mk_integer' b1 == mk_integer' b2) ==> (b1 == b2))
= Classical.move_requires (mk_integer'_inj' b1) b2

let parse_untagged_bounded_integer_kind (bound: pos) : LP.parser_kind = {
  LP.parser_kind_low = 1;
  LP.parser_kind_high = Some bound;
  LP.parser_kind_subkind = None;
  LP.parser_kind_metadata = None;
  LP.parser_kind_injective = true;
}

let parse_untagged_bounded_integer'
  (bound: pos)
  (x: LP.bytes)
: Tot (option (integer_in_interval bound & LP.consumed_length x))
= let l = Seq.length x in
  if l > bound
  then None
  else if valid_unsigned_repr x
  then begin
    mk_integer'_eq' x;
    let l = Seq.length x in
    let r = mk_integer' x in
    interval_intro l r;
    interval_weaken l bound r;
    Some (r, l)
  end else
    None

let parse_untagged_bounded_integer
  (bound: pos)
: Tot (LP.parser (parse_untagged_bounded_integer_kind bound) (integer_in_interval bound))
= Classical.forall_intro_2 mk_integer'_inj;
  LP.parser_kind_prop_equiv (parse_untagged_bounded_integer_kind bound) (parse_untagged_bounded_integer' bound);
  parse_untagged_bounded_integer' bound

let tag_of_integer_payload
  (x: int)
: Tot nat
= domain_intro_gen x

let synth_integer_payload
  (tag: nat)
  (x: integer_in_domain tag)
: Tot (LP.refine_with_tag tag_of_integer_payload tag)
= domain_unique tag (tag_of_integer_payload x) x;
  x

inline_for_extraction
//noextract
let parse_integer_payload_kind : LP.parser_kind =
  let open LP in
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None;
    parser_kind_injective = true;
  }

let parse_integer_payload
  (tag: nat)
: Tot (LP.parser parse_integer_payload_kind (LP.refine_with_tag (tag_of_integer_payload) tag))
= LP.weaken parse_integer_payload_kind (parse_integer_of_size tag)
  `LP.parse_synth` synth_integer_payload tag

let parse_integer
  (#kt: LP.parser_kind)
  (p: LP.parser kt nat {
    kt.LP.parser_kind_subkind == Some LP.ParserStrong
  })
: Tot (LP.parser (kt `LP.and_then_kind` parse_integer_payload_kind) int)
= LP.parse_tagged_union
    p
    (tag_of_integer_payload)
    (parse_integer_payload)

(* Serializer *)

let mk_bytes
  (n: nat)
  (x: int)
: Pure (Seq.lseq LP.byte n)
    (requires (domain n x))
    (ensures (fun s ->
      valid_unsigned_repr s /\
      mk_integer' s == x
    ))
= assert_norm (pow2 8 == 256);
  assert_norm (pow2 7 == 128);
  if (n = 1 && (x = 0 || x = -1))
  then
    if x = 0
    then begin
      let s = Seq.create 1 0uy in
      be_to_n_singleton s;
      s
    end else begin
      let s = Seq.create 1 255uy in
      be_to_n_singleton s;
      s
    end
  else begin
    Classical.move_requires (inner_positive_interval_elim n) x;
    Classical.move_requires (inner_negative_interval_elim n) x;
    Classical.move_requires (outer_positive_interval_elim n) x;
    Classical.move_requires (outer_negative_interval_elim n) x;
    if x >= 0
    then begin
      let s = E.n_to_be n x in
      mk_integer'_eq s;
      s
    end else begin
      let s = E.n_to_be n (x + pow2 (8 * n)) in
      mk_integer'_eq s;
      s
    end
  end

let serialize_integer_of_size
  (sz: nat)
: Tot (LP.serializer (parse_integer_of_size sz))
= fun (x: integer_in_domain sz) -> mk_bytes sz x

let synth_bounded_integer_payload_recip
  (bound: nat)
  (tag: bounded_integer_tag bound)
  (x: LP.refine_with_tag (tag_of_bounded_integer_payload bound) tag)
: Tot (integer_in_domain tag)
= x

let serialize_bounded_integer_payload
  (bound: nat)
  (tag: bounded_integer_tag bound)
: Tot (LP.serializer (parse_bounded_integer_payload bound tag))
= LP.serialize_synth
    _
    (synth_bounded_integer_payload bound tag)
    (LP.serialize_weaken _ (serialize_integer_of_size tag))
    (synth_bounded_integer_payload_recip bound tag)
    ()

let serialize_bounded_integer
  (bound: nat)
  (#kt: LP.parser_kind)
  (#p: LP.parser kt (bounded_integer_tag bound))
  (s: LP.serializer p {
    kt.LP.parser_kind_subkind == Some LP.ParserStrong
  })
: Tot (LP.serializer (parse_bounded_integer bound p))
= LP.serialize_tagged_union
    s
    (tag_of_bounded_integer_payload bound)
    (serialize_bounded_integer_payload bound)

let serialize_untagged_bounded_integer
  (bound: pos)
: Tot (LP.serializer (parse_untagged_bounded_integer bound))
= (fun (x: integer_in_interval bound) ->
    let d = interval_elim bound x in
    mk_bytes d x <: LP.bytes
  )

let synth_integer_payload_recip
  (tag: nat)
  (x: LP.refine_with_tag (tag_of_integer_payload) tag)
: Tot (integer_in_domain tag)
= x

let serialize_integer_payload
  (tag: nat)
: Tot (LP.serializer (parse_integer_payload tag))
= LP.serialize_synth
    _
    (synth_integer_payload tag)
    (LP.serialize_weaken _ (serialize_integer_of_size tag))
    (synth_integer_payload_recip tag)
    ()

let serialize_integer
  (#kt: LP.parser_kind)
  (#p: LP.parser kt nat)
  (s: LP.serializer p {
    kt.LP.parser_kind_subkind == Some LP.ParserStrong
  })
: Tot (LP.serializer (parse_integer p))
= LP.serialize_tagged_union
    s
    (tag_of_integer_payload)
    (serialize_integer_payload)

#pop-options

(* Implementations with machine integer types *)

inline_for_extraction
// noextract
noeq
type int_t (nbytes: pos) (i_t: Type0) = {
  v: (i_t -> Tot (integer_in_interval nbytes));
  int_to_t: (integer_in_interval nbytes -> Tot i_t);
  v_int_to_t: ((x: integer_in_interval nbytes) -> Lemma (v (int_to_t x) == x));
  int_to_t_v: ((x: i_t) -> Lemma (int_to_t (v x) == x));
}

let parse_untagged_signed_integer
  (#nbytes: pos)
  (#i_t: Type0)
  (i: int_t nbytes i_t)
: Tot (LP.parser (parse_untagged_bounded_integer_kind nbytes) i_t)
= Classical.forall_intro i.v_int_to_t;
  parse_untagged_bounded_integer nbytes `LP.parse_synth` (fun x -> i.int_to_t x)

module I32 = FStar.Int32

inline_for_extraction
// noextract
let int32: int_t 4 I32.t = {
  v = (fun x -> I32.v x);
  int_to_t = (fun x -> I32.int_to_t x);
  v_int_to_t = (fun _ -> ());
  int_to_t_v = (fun _ -> ());
}

let parse_untagged_int32
: LP.parser (parse_untagged_bounded_integer_kind 4) I32.t
= parse_untagged_signed_integer int32
