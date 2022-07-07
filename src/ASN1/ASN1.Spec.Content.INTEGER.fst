module ASN1.Spec.Content.INTEGER

module BF = LowParse.BitFields
module E = LowParse.Endianness.BitFields
module U = FStar.UInt
module U8 = FStar.UInt8

open FStar.Mul

// Make all integer proofs (pow2, etc.) explicit
#set-options "--z3cliopt smt.arith.nl=false --fuel 0"

let rec be_to_n_leading_zeros
  (s: Seq.seq U8.t)
: Lemma
  (requires (Seq.length s > 0))
  (ensures (
    E.be_to_n s < pow2 (8 * (Seq.length s - 1)) <==> U8.v (Seq.index s 0) == 0
  ))
  (decreases (Seq.length s))
= E.reveal_be_to_n s;
  let s' = Seq.slice s 0 (Seq.length s - 1) in
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

let outer_positive_interval_unique' (n1 n2: nat) (x: int) : Lemma
  (requires (n1 <= n2 /\ outer_positive_interval n1 x /\ outer_positive_interval n2 x))
  (ensures (n1 == n2))
= if n1 = n2
  then ()
  else FStar.Math.Lemmas.pow2_le_compat (8 * (n2 - 1)) (8 * n1 - 1)

let outer_positive_interval_unique (n1 n2: nat) (x: int) : Lemma
  (requires (outer_positive_interval n1 x /\ outer_positive_interval n2 x))
  (ensures (n1 == n2))
= if n1 <= n2
  then outer_positive_interval_unique' n1 n2 x
  else outer_positive_interval_unique' n2 n1 x

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

let inner_positive_interval_unique' (n1 n2: nat) (x: int) : Lemma
  (requires (n1 <= n2 /\ inner_positive_interval n1 x /\ inner_positive_interval n2 x))
  (ensures (n1 == n2))
= if n1 = n2
  then ()
  else FStar.Math.Lemmas.pow2_le_compat (8 * (n2 - 1) - 1) (8 * (n1 - 1))

let inner_positive_interval_unique (n1 n2: nat) (x: int) : Lemma
  (requires (inner_positive_interval n1 x /\ inner_positive_interval n2 x))
  (ensures (n1 == n2))
= if n1 <= n2
  then inner_positive_interval_unique' n1 n2 x
  else inner_positive_interval_unique' n2 n1 x

let inner_positive_not_outer (n1 n2: nat) (x: int) : Lemma
  (requires (
    inner_positive_interval n1 x /\ outer_positive_interval n2 x
  ))
  (ensures False)
= if n1 <= n2
  then FStar.Math.Lemmas.pow2_le_compat (8 * (n2 - 1)) (8 * (n1 - 1))
  else FStar.Math.Lemmas.pow2_le_compat (8 * (n1 - 1) - 1) (8 * n2 - 1)

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

let outer_negative_interval_unique' (n1 n2: nat) (x: int) : Lemma
  (requires (n1 <= n2 /\ outer_negative_interval n1 x /\ outer_negative_interval n2 x))
  (ensures (n1 == n2))
= if n1 = n2
  then ()
  else begin
    pow2_8_n_255 (n2 - 1);
    FStar.Math.Lemmas.pow2_plus (8 * n1 - 1) 1;
    FStar.Math.Lemmas.pow2_le_compat (8 * (n2 - 1)) (8 * n1 - 1)
  end

let outer_negative_interval_unique (n1 n2: nat) (x: int) : Lemma
  (requires (outer_negative_interval n1 x /\ outer_negative_interval n2 x))
  (ensures (n1 == n2))
= if n1 <= n2
  then outer_negative_interval_unique' n1 n2 x
  else outer_negative_interval_unique' n2 n1 x

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

let inner_negative_interval_unique' (n1 n2: nat) (x: int) : Lemma
  (requires (n1 <= n2 /\ inner_negative_interval n1 x /\ inner_negative_interval n2 x))
  (ensures (n1 == n2))
=
  inner_negative_interval_elim n1 x;
  inner_negative_interval_elim n2 x;
  be_to_n_chop_leading_ones_recip (E.n_to_be n1 (x + pow2 (8 * n1))) (E.n_to_be n2 (x + pow2 (8 * n2)))

let inner_negative_interval_unique (n1 n2: nat) (x: int) : Lemma
  (requires (inner_negative_interval n1 x /\ inner_negative_interval n2 x))
  (ensures (n1 == n2))
= if n1 <= n2
  then inner_negative_interval_unique' n1 n2 x
  else inner_negative_interval_unique' n2 n1 x

let negative_not_positive (n1 n2: nat) (x: int) : Lemma
  (requires (
    (outer_negative_interval n1 x \/ inner_negative_interval n1 x) /\
    (outer_positive_interval n2 x \/ inner_positive_interval n2 x)
  ))
  (ensures False)
= Classical.move_requires (outer_negative_interval_elim n1) x;
  Classical.move_requires (inner_negative_interval_elim n1) x;
  Classical.move_requires (outer_positive_interval_elim n2) x;
  Classical.move_requires (inner_positive_interval_elim n2) x

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
