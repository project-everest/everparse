module LowParse.BitFields
module U = FStar.UInt
module M = LowParse.Math

open FStar.Mul

inline_for_extraction
let bitfield_mask (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) : Tot (U.uint_t tot) =
  [@inline_let] let _ =
    M.pow2_le_compat tot hi;
    M.pow2_plus (hi - lo) lo
  in
  normalize_term ((pow2 (hi - lo) - 1) * pow2 lo)

let bitfield_mask_eq (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) : Lemma
  (
    0 <= pow2 (hi - lo) - 1 /\
    pow2 (hi - lo) - 1 < pow2 tot /\
    bitfield_mask tot lo hi == U.shift_left #tot (pow2 (hi - lo) - 1) lo
  )
=
  M.pow2_le_compat tot (hi - lo);
  U.shift_left_value_lemma #tot (pow2 (hi - lo) - 1) lo;
  M.pow2_le_compat tot hi;
  M.pow2_plus (hi - lo) lo;
  M.lemma_mult_nat (pow2 (hi - lo) - 1) (pow2 lo);
  M.lemma_mult_lt' (pow2 lo) (pow2 (hi - lo) - 1) (pow2 (hi - lo));
  M.swap_mul (pow2 (hi - lo)) (pow2 lo);
  M.swap_mul (pow2 (hi - lo) - 1) (pow2 lo);
  M.modulo_lemma ((pow2 (hi - lo) - 1) * pow2 lo) (pow2 tot)

(* Cf. U.index_to_vec_ones; WHY WHY WHY is it private? *)
val nth_pow2_minus_one' : #n:pos -> m:nat{m <= n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (pow2 m <= pow2 n /\
          (i < n - m ==> U.nth #n (pow2 m - 1) i == false) /\
          (n - m <= i ==> U.nth #n (pow2 m - 1) i == true)))
let rec nth_pow2_minus_one' #n m i =
   let a = pow2 m - 1 in
   M.pow2_le_compat n m;
   if m = 0 then U.one_to_vec_lemma #n i
   else if m = n then U.ones_to_vec_lemma #n i
   else if i = n - 1 then ()
   else nth_pow2_minus_one' #(n - 1) (m - 1) i

(* Rephrasing with a more natural nth *)

let nth (#n: pos) (a: U.uint_t n) (i: nat {i < n}) : Tot bool =
  U.nth a (n - 1 - i)

let eq_nth
  (#n: pos)
  (a: U.uint_t n)
  (b: U.uint_t n)
  (f: (
    (i: nat { i < n }) ->
    Lemma
    (nth a i == nth b i)
  ))
: Lemma
  (a == b)
= let g
    (i: nat { i < n })
  : Lemma
    (U.nth a i == U.nth b i)
  = f (n - 1 - i)
  in
  Classical.forall_intro g;
  U.nth_lemma a b

let nth_pow2_minus_one
  (#n:pos)
  (m:nat{m <= n})
  (i:nat{i < n})
: Lemma (requires True)
        (ensures (pow2 m <= pow2 n /\
          (nth #n (pow2 m - 1) i == (i < m))))
= nth_pow2_minus_one' #n m (n - 1 - i)

let nth_shift_left
  (#n: pos)
  (a: U.uint_t n)
  (s: nat)
  (i: nat {i < n})
: Lemma
  (nth (U.shift_left a s) i == (s <= i && nth a (i - s)))
= ()

let nth_shift_right
  (#n: pos)
  (a: U.uint_t n)
  (s: nat)
  (i: nat {i < n})
: Lemma
  (nth (U.shift_right a s) i == (i + s < n && nth a (i + s)))
= ()

let nth_bitfield_mask (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (i: nat {i < tot}) : Lemma
  (nth (bitfield_mask tot lo hi) i == (lo <= i && i < hi))
=   bitfield_mask_eq tot lo hi;
    nth_shift_left #tot (pow2 (hi - lo) - 1) lo i;
    if i < lo
    then ()
    else begin
      nth_pow2_minus_one #tot (hi - lo) (i - lo)
    end

let get_bitfield_raw (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot}) : Tot (U.uint_t tot) =
  (x `U.logand` bitfield_mask tot lo hi) `U.shift_right` lo

let nth_logand
  (#n: pos)
  (a b: U.uint_t n)
  (i: nat {i < n})
: Lemma
  (nth (a `U.logand` b) i == (nth a i && nth b i))
= ()

let nth_logor
  (#n: pos)
  (a b: U.uint_t n)
  (i: nat {i < n})
: Lemma
  (nth (a `U.logor` b) i == (nth a i || nth b i))
= ()

let nth_lognot
  (#n: pos)
  (a: U.uint_t n)
  (i: nat {i < n})
: Lemma
  (nth (U.lognot a) i == not (nth a i))
= ()

let nth_get_bitfield_raw (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot}) (i: nat {i < tot}) : Lemma
  (nth (get_bitfield_raw x lo hi) i == (i < hi - lo && nth x (i + lo)))
= nth_shift_right (x `U.logand` bitfield_mask tot lo hi) lo i;
  if i + lo < tot
  then begin
    nth_logand x (bitfield_mask tot lo hi) (i + lo);
    nth_bitfield_mask tot lo hi (i + lo)
  end else
    ()

let get_bitfield_raw_eq_logand_pow2_hi_lo_minus_one (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot}) : Lemma
  (let y = get_bitfield_raw x lo hi in
    pow2 (hi - lo) - 1 < pow2 tot /\
    y == y `U.logand` (pow2 (hi - lo) - 1)
  )
= nth_pow2_minus_one #tot (hi - lo) 0;
  let y = get_bitfield_raw x lo hi in
  eq_nth y (y `U.logand` (pow2 (hi - lo) - 1)) (fun i ->
    nth_get_bitfield_raw x lo hi i;
    nth_pow2_minus_one #tot (hi - lo) i;
    nth_logand y (pow2 (hi - lo) - 1) i
  )

#push-options "--z3rlimit 16"

let logand_mask
  (#n: pos)
  (a: U.uint_t n)
  (m: nat {m <= n})
: Lemma
  (pow2 m <= pow2 n /\
   U.logand a (pow2 m - 1) == a % pow2 m)
= M.pow2_le_compat n m;
  if m = 0
  then begin
    U.logand_lemma_1 a
  end else if m = n
  then begin
    U.logand_lemma_2 a;
    M.modulo_lemma a (pow2 m)
  end else begin
    U.logand_mask a m
  end

#pop-options

let nth_le_pow2_m
  (#n: pos)
  (a: U.uint_t n)
  (m: nat {m <= n})
  (i: nat {i < n})
: Lemma
  (requires (a < pow2 m /\ m <= i))
  (ensures (nth a i == false))
= logand_mask a m;
  M.modulo_lemma a (pow2 m);
  nth_pow2_minus_one #n m i;
  nth_logand a (pow2 m - 1) i

let get_bitfield_raw_bounded
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Lemma
  (get_bitfield_raw x lo hi < pow2 (hi - lo))
= get_bitfield_raw_eq_logand_pow2_hi_lo_minus_one x lo hi;
  logand_mask (get_bitfield_raw x lo hi) (hi - lo);
  M.lemma_mod_lt x (pow2 (hi - lo))

let get_bitfield 
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Tot (ubitfield tot (hi - lo))
= get_bitfield_raw_bounded x lo hi;
  get_bitfield_raw x lo hi

let nth_get_bitfield (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot}) (i: nat {i < tot}) : Lemma
  (nth (get_bitfield x lo hi) i == (i < hi - lo && nth x (i + lo)))
= nth_get_bitfield_raw x lo hi i

let get_bitfield_logor
  (#tot: pos) (x y: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Lemma
  (get_bitfield (x `U.logor` y) lo hi == get_bitfield x lo hi `U.logor` get_bitfield y lo hi)
= eq_nth (get_bitfield (x `U.logor` y) lo hi) (get_bitfield x lo hi `U.logor` get_bitfield y lo hi) (fun i ->
    nth_get_bitfield (x `U.logor` y) lo hi i;
    nth_get_bitfield x lo hi i;
    nth_get_bitfield y lo hi i
  )

let get_bitfield_logxor
  (#tot: pos) (x y: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot})
: Lemma
  (get_bitfield (x `U.logxor` y) lo hi == get_bitfield x lo hi `U.logxor` get_bitfield y lo hi)
= eq_nth (get_bitfield (x `U.logxor` y) lo hi) (get_bitfield x lo hi `U.logxor` get_bitfield y lo hi) (fun i ->
    nth_get_bitfield (x `U.logxor` y) lo hi i;
    nth_get_bitfield x lo hi i;
    nth_get_bitfield y lo hi i
  )

#push-options "--z3rlimit 16"

let logor_disjoint
  (#n: pos)
  (a: U.uint_t n)
  (b: U.uint_t n)
  (m: nat {m <= n})
: Lemma
  (requires (
    a % pow2 m == 0 /\
    b < pow2 m
  ))
  (ensures (U.logor #n a b == a + b))
= if m = 0
  then
    U.logor_lemma_1 a
  else if m = n
  then begin
    M.modulo_lemma a (pow2 n);
    U.logor_commutative a b;
    U.logor_lemma_1 b
  end else
    U.logor_disjoint a b m

#pop-options

let bitfield_mask_mod_pow2_lo
  (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (m: nat {m <= lo})
: Lemma
  (bitfield_mask tot lo hi % pow2 m == 0)
= M.pow2_multiplication_modulo_lemma_1 (pow2 (hi - lo) - 1) m lo

let bitfield_mask_lt_pow2_hi
  (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (bitfield_mask tot lo hi < pow2 hi)
= 
    M.pow2_le_compat tot hi;
    M.pow2_plus (hi - lo) lo

inline_for_extraction
let not_bitfield_mask (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Tot (x: U.uint_t tot {x == U.lognot (bitfield_mask tot lo hi)})
= [@inline_let] 
  let a = bitfield_mask tot hi tot in
  [@inline_let]
  let b = bitfield_mask tot 0 lo in
  [@inline_let]
  let _ =
    bitfield_mask_mod_pow2_lo tot hi tot lo;
    bitfield_mask_lt_pow2_hi tot 0 lo;
    logor_disjoint a b lo;
    eq_nth (a `U.logor` b) (U.lognot (bitfield_mask tot lo hi)) (fun i ->
      nth_bitfield_mask tot hi tot i;
      nth_bitfield_mask tot 0 lo i;
      nth_bitfield_mask tot lo hi i
    )
  in
  normalize_term (a + b)

let nth_not_bitfield_mask (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (i: nat {i < tot}) : Lemma
  (nth (not_bitfield_mask tot lo hi) i == (i < lo || hi <= i))
= nth_lognot (bitfield_mask tot lo hi) i;
  nth_bitfield_mask tot lo hi i

let set_bitfield
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
: Tot (U.uint_t tot)
= (x `U.logand` not_bitfield_mask tot lo hi) `U.logor` (v `U.shift_left` lo)

let nth_set_bitfield
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (i: nat {i < tot})
: Lemma
  (nth (set_bitfield x lo hi v) i == (if lo <= i && i < hi then nth v (i - lo) else nth x i))
=
  let y = nth (set_bitfield x lo hi v) i in
  nth_logor (x `U.logand` not_bitfield_mask tot lo hi) (v `U.shift_left` lo) i;
  assert (y == (nth (x `U.logand` not_bitfield_mask tot lo hi) i || nth (v `U.shift_left` lo) i));
  nth_logand x (not_bitfield_mask tot lo hi) i;
  assert (y == ((nth x i && nth (not_bitfield_mask tot lo hi) i) || nth (v `U.shift_left` lo) i));
  nth_not_bitfield_mask tot lo hi i;
  assert (y == ((nth x i && (i < lo || hi <= i)) || nth (v `U.shift_left` lo) i));
  nth_shift_left v lo i;
  assert (y == ((nth x i && (i < lo || hi <= i)) || (lo <= i && nth v (i - lo))));
  if (lo <= i && i < hi) then
    assert (y == nth v (i - lo))
  else if (i < hi)
  then
    assert (y == nth x i)
  else begin
    nth_le_pow2_m v (hi - lo) (i - lo);
    assert (y == nth x i)
  end;
  assert (y == (if lo <= i && i < hi then nth v (i - lo) else nth x i))

#push-options "--z3rlimit 32"
let get_bitfield_set_bitfield_same
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
: Lemma
  (get_bitfield (set_bitfield x lo hi v) lo hi == v)
= eq_nth (get_bitfield (set_bitfield x lo hi v) lo hi) v (fun i ->
    nth_get_bitfield (set_bitfield x lo hi v) lo hi i;
    if i < hi - lo
    then begin
      nth_set_bitfield x lo hi v (i + lo)
    end else
      nth_le_pow2_m v (hi - lo) i
  )
#pop-options

let get_bitfield_set_bitfield_other
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot })
: Lemma
  (requires (hi' <= lo \/ hi <= lo'))
  (ensures (get_bitfield (set_bitfield x lo hi v) lo' hi' == get_bitfield x lo' hi'))
= eq_nth (get_bitfield (set_bitfield x lo hi v) lo' hi') (get_bitfield x lo' hi') (fun i ->
    nth_get_bitfield (set_bitfield x lo hi v) lo' hi' i;
    nth_get_bitfield x lo' hi' i;
    if i < hi' - lo'
    then begin
      nth_set_bitfield x lo hi v (i + lo')
    end
  )

let set_bitfield_set_bitfield_same_gen
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= lo /\ hi <= hi' /\ hi' <= tot })
  (v' : ubitfield tot (hi' - lo'))
: Lemma
  (ensures (set_bitfield (set_bitfield x lo hi v) lo' hi' v' == set_bitfield x lo' hi' v'))
= eq_nth (set_bitfield (set_bitfield x lo hi v) lo' hi' v') (set_bitfield x lo' hi' v') (fun i ->
    nth_set_bitfield (set_bitfield x lo hi v) lo' hi' v' i;
    nth_set_bitfield x lo hi v i;
    nth_set_bitfield x lo' hi' v' i
  )

let set_bitfield_set_bitfield_other
  (#tot: pos) (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
  (lo' : nat) (hi' : nat { lo' <= hi' /\ hi' <= tot }) (v' : ubitfield tot (hi' - lo'))
: Lemma
  (requires (hi' <= lo \/ hi <= lo'))
  (ensures (set_bitfield (set_bitfield x lo hi v) lo' hi' v' == set_bitfield (set_bitfield x lo' hi' v') lo hi v))
= eq_nth (set_bitfield (set_bitfield x lo hi v) lo' hi' v') (set_bitfield (set_bitfield x lo' hi' v') lo hi v) (fun i ->
    nth_set_bitfield (set_bitfield x lo hi v) lo' hi' v' i;
    nth_set_bitfield x lo hi v i;
    nth_set_bitfield (set_bitfield x lo' hi' v') lo hi v i;
    nth_set_bitfield x lo' hi' v' i
  )

let set_bitfield_full
  (#tot: pos) (x: U.uint_t tot) (y: ubitfield tot tot)
: Lemma
  (set_bitfield x 0 tot y == y)
= eq_nth (set_bitfield x 0 tot y) y (fun i ->
    nth_set_bitfield x 0 tot y i
  )

let set_bitfield_empty
  (#tot: pos) (x: U.uint_t tot) (i: nat { i <= tot }) (y: ubitfield tot 0)
: Lemma
  (set_bitfield x i i y == x)
= eq_nth (set_bitfield x i i y) x (fun j ->
    nth_set_bitfield x i i y j
  )

let nth_zero
  (tot: pos)
  (i: nat {i < tot})
: Lemma
  (nth #tot 0 i == false)
= U.zero_nth_lemma #tot i

let get_bitfield_zero
  (tot: pos)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (get_bitfield #tot 0 lo hi == 0)
= eq_nth (get_bitfield #tot 0 lo hi) 0 (fun i ->
    nth_zero tot i;
    nth_get_bitfield #tot 0 lo hi i;
    if i < hi - lo
    then nth_zero tot (i + lo)
  )

let get_bitfield_full
  (#tot: pos)
  (x: U.uint_t tot)
: Lemma
  (get_bitfield x 0 tot == x)
= eq_nth (get_bitfield x 0 tot) x (fun i ->
    nth_get_bitfield x 0 tot i
  )

let get_bitfield_empty
  (#tot: pos)
  (x: U.uint_t tot)
  (i: nat { i <= tot })
: Lemma
  (get_bitfield x i i == 0)
= eq_nth (get_bitfield x i i) 0 (fun j ->
    nth_get_bitfield x i i j;
    nth_zero tot j
  )

let lt_pow2_get_bitfield_hi
  (#tot: pos)
  (x: U.uint_t tot)
  (mi: nat {mi <= tot})
: Lemma
  (requires (x < pow2 mi))
  (ensures (get_bitfield x mi tot == 0))
= if mi = 0
  then get_bitfield_zero tot mi tot
  else if mi < tot
  then begin
    M.modulo_lemma x (pow2 mi);
    U.logand_mask x mi;
    eq_nth (get_bitfield x mi tot) 0 (fun i ->
      nth_zero tot i;
      nth_get_bitfield x mi tot i;
      nth_get_bitfield (x `U.logand` (pow2 mi - 1)) mi tot i;
      nth_pow2_minus_one #tot mi i
    )
  end

let get_bitfield_hi_lt_pow2
  (#tot: pos)
  (x: U.uint_t tot)
  (mi: nat {mi <= tot})
: Lemma
  (requires (get_bitfield x mi tot == 0))
  (ensures (x < pow2 mi))
= if mi = 0
  then get_bitfield_full x
  else if mi < tot
  then begin
    M.pow2_le_compat tot mi;
    eq_nth x (x `U.logand` (pow2 mi - 1)) (fun i ->
      nth_pow2_minus_one #tot mi i;
      if mi <= i
      then begin
        nth_get_bitfield x mi tot (i - mi);
        nth_zero tot (i - mi)
      end
    );
    U.logand_mask x mi;
    M.lemma_mod_lt x (pow2 mi)
  end

let get_bitfield_get_bitfield
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (lo': nat) (hi': nat { lo' <= hi' /\ hi' <= hi - lo })
: Lemma
  (get_bitfield (get_bitfield x lo hi) lo' hi' == get_bitfield x (lo + lo') (lo + hi'))
= eq_nth (get_bitfield (get_bitfield x lo hi) lo' hi') (get_bitfield x (lo + lo') (lo + hi')) (fun i ->
    nth_get_bitfield (get_bitfield x lo hi) lo' hi' i;
    nth_get_bitfield x (lo + lo') (lo + hi') i ;
    if i < hi' - lo'
    then nth_get_bitfield x lo hi (i + lo')
  )

#push-options "--z3rlimit_factor 2"
let get_bitfield_zero_inner
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (lo': nat { lo <= lo' }) (hi': nat { lo' <= hi' /\ hi' <= hi })
: Lemma
  (ensures (get_bitfield x lo hi == 0 ==> get_bitfield x lo' hi' == 0))
= let f () : Lemma
    (requires (get_bitfield x lo hi == 0))
    (ensures (get_bitfield x lo' hi' == 0))
  =
    eq_nth (get_bitfield x lo' hi') 0 (fun i ->
      nth_get_bitfield x lo' hi' i;
      nth_zero tot i;
      if (i < hi' - lo') then begin
        nth_get_bitfield x lo hi (i + lo' - lo);
        nth_zero tot (i + lo');
        nth_zero tot (i + lo' - lo)
      end
    )
  in
  Classical.move_requires f ()
#pop-options

#push-options "--z3rlimit 32"
let bitfield_is_zero
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (get_bitfield x lo hi == 0 <==>  x `U.logand` bitfield_mask tot lo hi == 0)
= 
  let y = x `U.logand` bitfield_mask tot lo hi in
  let z = get_bitfield x lo hi in
  let f () : Lemma
    (requires (y == 0))
    (ensures (z == 0))
  = eq_nth z 0 (fun i ->
      nth_zero tot i;
      nth_logand x (bitfield_mask tot lo hi) i;
      nth_bitfield_mask tot lo hi i;
      nth_get_bitfield x lo hi i;
      if i < hi - lo
      then nth_zero tot (i + lo)
    )
  in
  let g () : Lemma
    (requires (z == 0))
    (ensures (y == 0))
  = eq_nth y 0 (fun i ->
      nth_zero tot i;
      nth_logand x (bitfield_mask tot lo hi) i;
      nth_bitfield_mask tot lo hi i;
      if lo <= i && i < hi
      then begin
        nth_get_bitfield x lo hi (i - lo);
        nth_zero tot (i - lo)
      end
    )
  in
  Classical.move_requires f ();
  Classical.move_requires g ()
#pop-options

#push-options "--z3rlimit 16"

let bitfield_eq_shift
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
  (v: ubitfield tot (hi - lo))
: Lemma
  (get_bitfield x lo hi == v <==>  x `U.logand` bitfield_mask tot lo hi == v `U.shift_left` lo)
= 
  let y = x `U.logand` bitfield_mask tot lo hi in
  let z = get_bitfield x lo hi in
  let w = v `U.shift_left` lo in
  let f () : Lemma
    (requires (y == w))
    (ensures (z == v))
  = eq_nth z v (fun i ->
      nth_logand x (bitfield_mask tot lo hi) i;
      nth_bitfield_mask tot lo hi i;
      nth_get_bitfield x lo hi i;
      if hi - lo <= i
      then nth_le_pow2_m v (hi - lo) i
      else nth_shift_left v lo (i + lo)
    )
  in
  let g () : Lemma
    (requires (z == v))
    (ensures (y == w))
  = eq_nth y w (fun i ->
      nth_logand x (bitfield_mask tot lo hi) i;
      nth_bitfield_mask tot lo hi i;
      nth_shift_left v lo i;
      if hi <= i
      then
        nth_le_pow2_m v (hi - lo) (i - lo)
      else if lo <= i
      then begin
        nth_get_bitfield x lo hi (i - lo)
      end
    )
  in
  Classical.move_requires f ();
  Classical.move_requires g ()

#pop-options

#push-options "--z3rlimit 16"
let set_bitfield_get_bitfield
  (#tot: pos)
  (x: U.uint_t tot)
  (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (set_bitfield x lo hi (get_bitfield x lo hi) == x)
= eq_nth (set_bitfield x lo hi (get_bitfield x lo hi)) x (fun i ->
    nth_set_bitfield x lo hi (get_bitfield x lo hi) i;
    if lo <= i && i < hi
    then nth_get_bitfield x lo hi (i - lo)
  )
#pop-options

#push-options "--z3rlimit 16"

let get_bitfield_partition_2_gen
  (#tot: pos)
  (lo: nat)
  (mi: nat)
  (hi: nat { lo <= mi /\ mi <= hi /\ hi <= tot })
  (x y: U.uint_t tot)
: Lemma
  (requires (
    get_bitfield x lo mi == get_bitfield y lo mi /\
    get_bitfield x mi hi == get_bitfield y mi hi
  ))
  (ensures (
    get_bitfield x lo hi == get_bitfield y lo hi
  ))
= eq_nth (get_bitfield x lo hi) (get_bitfield y lo hi) (fun i ->
    let a = nth (get_bitfield x lo hi) i in
    let b = nth (get_bitfield y lo hi) i in
    nth_get_bitfield x lo hi i;
    nth_get_bitfield y lo hi i;
    if i < hi - lo
    then begin
      if i < mi - lo
      then begin
        nth_get_bitfield x lo mi i;
        nth_get_bitfield y lo mi i
      end else begin
        nth_get_bitfield x mi hi (i + lo - mi); 
        nth_get_bitfield y mi hi (i + lo - mi)
      end
    end
  )

#pop-options

let get_bitfield_partition_2
  (#tot: pos)
  (mid: nat { mid <= tot })
  (x y: U.uint_t tot)  
: Lemma
  (requires (
    get_bitfield x 0 mid == get_bitfield y 0 mid /\
    get_bitfield x mid tot == get_bitfield y mid tot
  ))
  (ensures (
    x == y
  ))
= get_bitfield_partition_2_gen 0 mid tot x y;
  get_bitfield_full x;
  get_bitfield_full y

let rec get_bitfield_partition'
  (#tot: pos)
  (x y: U.uint_t tot)
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot })
  (l: list nat)
: Lemma
  (requires (get_bitfield_partition_prop x y lo hi l))
  (ensures (get_bitfield x lo hi == get_bitfield y lo hi))
  (decreases l)
= match l with
  | [] -> ()
  | mi :: q ->
    get_bitfield_partition' x y mi hi q;
    get_bitfield_partition_2_gen lo mi hi x y

let get_bitfield_partition = get_bitfield_partition'

let rec nth_size (n1: nat) (n2: nat { n1 <= n2 }) (x: U.uint_t n1) (i: nat { i < n2 }) : Lemma
  (x < pow2 n2 /\ nth #n2 x i == (i < n1 && nth #n1 x i))
= M.pow2_le_compat n2 n1;
  if i < n1
  then begin
    if i = 0
    then ()
    else nth_size (n1 - 1) (n2 - 1) (x / 2) (i - 1)
  end else nth_le_pow2_m #n2 x n1 i

let get_bitfield_size
  (tot1 tot2: pos)
  (x: nat { x < pow2 tot1 /\ tot1 <= tot2 })
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot1 })
: Lemma
  (x < pow2 tot2 /\ (get_bitfield #tot1 x lo hi <: nat) == (get_bitfield #tot2 x lo hi <: nat))
= M.pow2_le_compat tot2 tot1;
  eq_nth #tot2 (get_bitfield #tot1 x lo hi) (get_bitfield #tot2 x lo hi) (fun i ->
    let y1 = nth #tot2 (get_bitfield #tot1 x lo hi) i in
    let y2 = nth #tot2 (get_bitfield #tot2 x lo hi) i in
    nth_get_bitfield #tot2 x lo hi i;
    assert (y2 == (i < hi - lo && nth #tot2 x (i + lo)));
    nth_size tot1 tot2 (get_bitfield #tot1 x lo hi) i;
    assert (y1 == (i < tot1 && nth #tot1 (get_bitfield #tot1 x lo hi) i));
    if i < tot1
    then begin
      nth_get_bitfield #tot1 x lo hi i;
      assert (y1 == (i < hi - lo && nth #tot1 x (i + lo)));
      if i < hi - lo
      then nth_size tot1 tot2 x (i + lo)
    end
  )

let set_bitfield_size
  (tot1 tot2: pos)
  (x: nat { x < pow2 tot1 /\ tot1 <= tot2 })
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= tot1 })
  (v: ubitfield tot1 (hi - lo))
: Lemma
  (x < pow2 tot2 /\  v < pow2 tot2 /\ (set_bitfield #tot1 x lo hi v <: nat) == (set_bitfield #tot2 x lo hi v <: nat))
= M.pow2_le_compat tot2 tot1;
  eq_nth #tot2 (set_bitfield #tot1 x lo hi v) (set_bitfield #tot2 x lo hi v) (fun i ->
    let y1 = nth #tot2 (set_bitfield #tot1 x lo hi v) i in
    let y2 = nth #tot2 (set_bitfield #tot2 x lo hi v) i in
    nth_set_bitfield #tot2 x lo hi v i;
    nth_size tot1 tot2 (set_bitfield #tot1 x lo hi v) i;
    nth_size tot1 tot2 x i;
    if i < tot1
    then begin
      nth_set_bitfield #tot1 x lo hi v i;
      if lo <= i && i < hi
      then nth_size tot1 tot2 v (i - lo)
    end
  )

let set_bitfield_bound
  (#tot: pos)
  (x: U.uint_t tot)
  (bound: nat { bound <= tot /\ x < pow2 bound })
  (lo: nat)
  (hi: nat { lo <= hi /\ hi <= bound })
  (v: ubitfield tot (hi - lo))
: Lemma
  (set_bitfield x lo hi v < pow2 bound)
= if bound = 0
  then set_bitfield_empty x lo v
  else begin
    M.pow2_le_compat tot bound;
    M.pow2_le_compat bound (hi - lo);
    set_bitfield_size bound tot x lo hi v
  end

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --fuel 0 --ifuel 0"

let set_bitfield_set_bitfield_get_bitfield
  #tot x lo hi lo' hi' v'
= set_bitfield_bound (get_bitfield x lo hi) (hi - lo) lo' hi' v' ;
  let x1 = set_bitfield x lo hi (set_bitfield (get_bitfield x lo hi) lo' hi' v') in
  let x2 = set_bitfield x (lo + lo') (lo + hi') v' in
  eq_nth x1 x2 (fun i ->
    nth_set_bitfield x lo hi (set_bitfield (get_bitfield x lo hi) lo' hi' v') i;
    nth_set_bitfield x (lo + lo') (lo + hi') v' i ;
    if lo <= i && i < hi
    then begin
      assert (nth x1 i == nth (set_bitfield (get_bitfield x lo hi) lo' hi' v') (i - lo));
      nth_set_bitfield (get_bitfield x lo hi) lo' hi' v' (i - lo);
      if lo' <= i - lo && i - lo < hi'
      then begin
        ()
      end
      else begin
        assert (nth x2 i == nth x i);
        assert (nth x1 i == nth (get_bitfield x lo hi) (i - lo));
        nth_get_bitfield x lo hi (i - lo);
        assert (i - lo + lo == i)
      end
    end
  )

#pop-options

let mod_1 (x: int) : Lemma
  (x % 1 == 0)
= ()

let div_1 (x: int) : Lemma
  (x / 1 == x)
= ()

let get_bitfield_eq (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat {lo <= hi /\ hi <= tot}) : Lemma
  (get_bitfield x lo hi == (x / pow2 lo) % pow2 (hi - lo))
= if hi - lo = 0
  then begin
    assert (hi == lo);
    assert_norm (pow2 0 == 1);
    mod_1 (x / pow2 lo);
    get_bitfield_empty #tot x lo 
  end else if hi - lo = tot
  then begin
    assert (hi == tot);
    assert (lo == 0);
    assert_norm (pow2 0 == 1);
    div_1 x;
    M.small_mod x (pow2 tot);
    get_bitfield_full #tot x
  end else begin
    assert (hi - lo < tot);
    U.shift_right_logand_lemma #tot x (bitfield_mask tot lo hi) lo;
    U.shift_right_value_lemma #tot (bitfield_mask tot lo hi) lo;
    M.multiple_division_lemma (pow2 (hi - lo) - 1) (pow2 lo);
    U.logand_mask #tot (U.shift_right x lo) (hi - lo);
    U.shift_right_value_lemma #tot x lo
  end

let pow2_m_minus_one_eq
  (n: nat)
  (m: nat)
: Lemma
  (requires (m <= n))
  (ensures (
    (pow2 n - 1) / pow2 m == pow2 (n - m) - 1 
  ))
= M.pow2_le_compat n m;
  M.pow2_plus (n - m) m;
  M.division_definition (pow2 n - 1) (pow2 m) (pow2 (n - m) - 1)

let get_bitfield_eq_2
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot })
: Lemma
  (get_bitfield x lo hi == (x `U.shift_left` (tot - hi)) `U.shift_right` (tot - hi + lo))
= eq_nth (get_bitfield x lo hi) ((x `U.shift_left` (tot - hi)) `U.shift_right` (tot - hi + lo)) (fun i ->
    nth_get_bitfield x lo hi i;
    nth_shift_right (x `U.shift_left` (tot - hi)) (tot - hi + lo) i;
    let j = i + (tot - hi + lo) in
    if j < tot
    then nth_shift_left x (tot - hi) j
  )

#restart-solver
let bitfield_mask_eq_2 (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) : Lemma
  (
    bitfield_mask tot lo hi == U.shift_left #tot (U.lognot 0 `U.shift_right` (tot - (hi - lo))) lo
  )
= bitfield_mask_eq tot lo hi;
  pow2_m_minus_one_eq tot (tot - (hi - lo));
  U.lemma_lognot_value_mod #tot 0;
  U.shift_right_value_lemma #tot (pow2 tot - 1) (tot - (hi - lo))

let set_bitfield_eq
  (#tot: pos) (x: U.uint_t tot) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (v: ubitfield tot (hi - lo))
: Lemma
  (set_bitfield x lo hi v == (x `U.logand` U.lognot ((U.lognot 0 `U.shift_right` (tot - (hi - lo))) `U.shift_left` lo)) `U.logor` (v `U.shift_left` lo))
= bitfield_mask_eq_2 tot lo hi

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(* Instantiate to UInt64 *)

#push-options "--z3rlimit 32"

inline_for_extraction
let bitfield_mask64 (lo: nat) (hi: nat { lo <= hi /\ hi <= 64 }) : Tot (x: U64.t { U64.v x == bitfield_mask 64 lo hi }) =
  if lo = hi
  then 0uL
  else begin    
    bitfield_mask_eq_2 64 lo hi;
    (U64.lognot 0uL `U64.shift_right` (64ul `U32.sub` (U32.uint_to_t (hi - lo)))) `U64.shift_left` U32.uint_to_t lo
  end

inline_for_extraction
let u64_shift_right
  (x: U64.t)
  (amount: U32.t { U32.v amount <= 64 })
: Tot (y: U64.t { U64.v y == U64.v x `U.shift_right` U32.v amount })
= if amount = 64ul then 0uL else x `U64.shift_right` amount

inline_for_extraction
let get_bitfield64
  (x: U64.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 64})
: Tot (y: U64.t { U64.v y == get_bitfield (U64.v x) lo hi })
= (x `U64.logand` bitfield_mask64 lo hi) `u64_shift_right` (U32.uint_to_t lo)

inline_for_extraction
let not_bitfield_mask64 (lo: nat) (hi: nat { lo <= hi /\ hi <= 64 }) : Tot (x: U64.t { U64.v x == not_bitfield_mask 64 lo hi }) =
  U64.lognot (bitfield_mask64 lo hi)

inline_for_extraction
let u64_shift_left
  (x: U64.t)
  (amount: U32.t { U32.v amount <= 64 })
: Tot (y: U64.t { U64.v y == U64.v x `U.shift_left` U32.v amount })
= if amount = 64ul then 0uL else x `U64.shift_left` amount

inline_for_extraction
let set_bitfield64
  (x: U64.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 64})
  (v: U64.t { U64.v v < pow2 (hi - lo) })
: Tot (y: U64.t { U64.v y == set_bitfield (U64.v x) lo hi (U64.v v) })
= (x `U64.logand` not_bitfield_mask64 lo hi) `U64.logor` (v `u64_shift_left` U32.uint_to_t lo)

inline_for_extraction
let bitfield_eq64_lhs
  (x: U64.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 64})
: Tot U64.t
= x `U64.logand` bitfield_mask64 lo hi

#push-options "--z3rlimit 16"

inline_for_extraction
let bitfield_eq64_rhs
  (x: U64.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 64})
  (v: U64.t { U64.v v < pow2 (hi - lo) })
: Tot (y: U64.t { bitfield_eq64_lhs x lo hi == y <==> (get_bitfield64 x lo hi <: U64.t) == v })
= [@inline_let] let _ =
    bitfield_eq_shift (U64.v x) lo hi (U64.v v)
  in
  v `u64_shift_left` U32.uint_to_t lo

#pop-options

inline_for_extraction
let get_bitfield_gen64
  (x: U64.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 64})
: Tot (y: U64.t { U64.v y == get_bitfield (U64.v x) (U32.v lo) (U32.v hi) })
= get_bitfield_eq_2 #64 (U64.v x) (U32.v lo) (U32.v hi);
  (x `U64.shift_left` (64ul `U32.sub` hi)) `U64.shift_right` ((64ul `U32.sub` hi) `U32.add` lo)

inline_for_extraction
let set_bitfield_gen64
  (x: U64.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 64})
  (v: U64.t { U64.v v < pow2 (U32.v hi - U32.v lo) })
: Tot (y: U64.t { U64.v y == set_bitfield (U64.v x) (U32.v lo) (U32.v hi) (U64.v v) })
= bitfield_mask_eq_2 64 (U32.v lo) (U32.v hi);
  (x `U64.logand` U64.lognot (((U64.lognot 0uL) `U64.shift_right` (64ul `U32.sub` (hi `U32.sub` lo))) `U64.shift_left` lo)) `U64.logor` (v `U64.shift_left` lo)

(* Instantiate to UInt32 *)

inline_for_extraction
let bitfield_mask32 (lo: nat) (hi: nat { lo <= hi /\ hi <= 32 }) : Tot (x: U32.t { U32.v x == bitfield_mask 32 lo hi }) =
  if lo = hi
  then 0ul
  else begin    
    bitfield_mask_eq_2 32 lo hi;
    (U32.lognot 0ul `U32.shift_right` (32ul `U32.sub` (U32.uint_to_t (hi - lo)))) `U32.shift_left` U32.uint_to_t lo
  end

inline_for_extraction
let u32_shift_right
  (x: U32.t)
  (amount: U32.t { U32.v amount <= 32 })
: Tot (y: U32.t { U32.v y == U32.v x `U.shift_right` U32.v amount })
= if amount = 32ul then 0ul else x `U32.shift_right` amount

inline_for_extraction
let get_bitfield32
  (x: U32.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 32})
: Tot (y: U32.t { U32.v y == get_bitfield (U32.v x) lo hi })
= (x `U32.logand` bitfield_mask32 lo hi) `u32_shift_right` (U32.uint_to_t lo)

inline_for_extraction
let not_bitfield_mask32 (lo: nat) (hi: nat { lo <= hi /\ hi <= 32 }) : Tot (x: U32.t { U32.v x == not_bitfield_mask 32 lo hi }) =
  U32.lognot (bitfield_mask32 lo hi)

inline_for_extraction
let u32_shift_left
  (x: U32.t)
  (amount: U32.t { U32.v amount <= 32 })
: Tot (y: U32.t { U32.v y == U32.v x `U.shift_left` U32.v amount })
= if amount = 32ul then 0ul else x `U32.shift_left` amount

inline_for_extraction
let set_bitfield32
  (x: U32.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 32})
  (v: U32.t { U32.v v < pow2 (hi - lo) })
: Tot (y: U32.t { U32.v y == set_bitfield (U32.v x) lo hi (U32.v v) })
= (x `U32.logand` not_bitfield_mask32 lo hi) `U32.logor` (v `u32_shift_left` U32.uint_to_t lo)

inline_for_extraction
let bitfield_eq32_lhs
  (x: U32.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 32})
: Tot U32.t
= x `U32.logand` bitfield_mask32 lo hi

inline_for_extraction
let bitfield_eq32_rhs
  (x: U32.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 32})
  (v: U32.t { U32.v v < pow2 (hi - lo) })
: Tot (y: U32.t { bitfield_eq32_lhs x lo hi == y <==> (get_bitfield32 x lo hi <: U32.t) == v })
= [@inline_let] let _ =
    bitfield_eq_shift (U32.v x) lo hi (U32.v v)
  in
  v `u32_shift_left` U32.uint_to_t lo

inline_for_extraction
let get_bitfield_gen32
  (x: U32.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 32})
: Tot (y: U32.t { U32.v y == get_bitfield (U32.v x) (U32.v lo) (U32.v hi) })
= get_bitfield_eq_2 #32 (U32.v x) (U32.v lo) (U32.v hi);
  (x `U32.shift_left` (32ul `U32.sub` hi)) `U32.shift_right` ((32ul `U32.sub` hi) `U32.add` lo)

#push-options "--z3rlimit 16"

inline_for_extraction
let set_bitfield_gen32
  (x: U32.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 32})
  (v: U32.t { U32.v v < pow2 (U32.v hi - U32.v lo) })
: Tot (y: U32.t { U32.v y == set_bitfield (U32.v x) (U32.v lo) (U32.v hi) (U32.v v) })
= bitfield_mask_eq_2 32 (U32.v lo) (U32.v hi);
  (x `U32.logand` U32.lognot (((U32.lognot 0ul) `U32.shift_right` (32ul `U32.sub` (hi `U32.sub` lo))) `U32.shift_left` lo)) `U32.logor` (v `U32.shift_left` lo)

#pop-options

(* Instantiate to UInt16 *)

inline_for_extraction
let bitfield_mask16 (lo: nat) (hi: nat { lo <= hi /\ hi <= 16 }) : Tot (x: U16.t { U16.v x == bitfield_mask 16 lo hi }) =
  if lo = hi
  then 0us
  else begin    
    bitfield_mask_eq_2 16 lo hi;
    (U16.lognot 0us `U16.shift_right` (16ul `U32.sub` (U32.uint_to_t (hi - lo)))) `U16.shift_left` U32.uint_to_t lo
  end

inline_for_extraction
let u16_shift_right
  (x: U16.t)
  (amount: U32.t { U32.v amount <= 16 })
: Tot (y: U16.t { U16.v y == U16.v x `U.shift_right` U32.v amount })
= if amount = 16ul then 0us else x `U16.shift_right` amount

inline_for_extraction
let get_bitfield16
  (x: U16.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 16})
: Tot (y: U16.t { U16.v y == get_bitfield (U16.v x) lo hi })
= (x `U16.logand` bitfield_mask16 lo hi) `u16_shift_right` (U32.uint_to_t lo)

inline_for_extraction
let not_bitfield_mask16 (lo: nat) (hi: nat { lo <= hi /\ hi <= 16 }) : Tot (x: U16.t { U16.v x == not_bitfield_mask 16 lo hi }) =
  U16.lognot (bitfield_mask16 lo hi)

inline_for_extraction
let u16_shift_left
  (x: U16.t)
  (amount: U32.t { U32.v amount <= 16 })
: Tot (y: U16.t { U16.v y == U16.v x `U.shift_left` U32.v amount })
= if amount = 16ul then 0us else x `U16.shift_left` amount

inline_for_extraction
let set_bitfield16
  (x: U16.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 16})
  (v: U16.t { U16.v v < pow2 (hi - lo) })
: Tot (y: U16.t { U16.v y == set_bitfield (U16.v x) lo hi (U16.v v) })
= (x `U16.logand` not_bitfield_mask16 lo hi) `U16.logor` (v `u16_shift_left` U32.uint_to_t lo)

inline_for_extraction
let bitfield_eq16_lhs
  (x: U16.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 16})
: Tot U16.t
= x `U16.logand` bitfield_mask16 lo hi

inline_for_extraction
let bitfield_eq16_rhs
  (x: U16.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 16})
  (v: U16.t { U16.v v < pow2 (hi - lo) })
: Tot (y: U16.t { bitfield_eq16_lhs x lo hi == y <==> (get_bitfield16 x lo hi <: U16.t) == v })
= [@inline_let] let _ =
    bitfield_eq_shift (U16.v x) lo hi (U16.v v)
  in
  v `u16_shift_left` U32.uint_to_t lo

inline_for_extraction
let get_bitfield_gen16
  (x: U16.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 16})
: Tot (y: U16.t { U16.v y == get_bitfield (U16.v x) (U32.v lo) (U32.v hi) })
= get_bitfield_eq_2 #16 (U16.v x) (U32.v lo) (U32.v hi);
  (* avoid integer promotion again *)
  let bf : U16.t = x `U16.shift_left` (16ul `U32.sub` hi) in
  bf `U16.shift_right` ((16ul `U32.sub` hi) `U32.add` lo)

inline_for_extraction
let set_bitfield_gen16
  (x: U16.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 16})
  (v: U16.t { U16.v v < pow2 (U32.v hi - U32.v lo) })
: Tot (y: U16.t { U16.v y == set_bitfield (U16.v x) (U32.v lo) (U32.v hi) (U16.v v) })
= bitfield_mask_eq_2 16 (U32.v lo) (U32.v hi);
  (x `U16.logand` U16.lognot (((U16.lognot 0us) `U16.shift_right` (16ul `U32.sub` (hi `U32.sub` lo))) `U16.shift_left` lo)) `U16.logor` (v `U16.shift_left` lo)

inline_for_extraction
let bitfield_mask8 (lo: nat) (hi: nat { lo <= hi /\ hi <= 8 }) : Tot (x: U8.t { U8.v x == bitfield_mask 8 lo hi }) =
  if lo = hi
  then 0uy
  else begin
    bitfield_mask_eq_2 8 lo hi;
    (U8.lognot 0uy `U8.shift_right` (8ul `U32.sub` (U32.uint_to_t (hi - lo)))) `U8.shift_left` U32.uint_to_t lo
  end

inline_for_extraction
let u8_shift_right
  (x: U8.t)
  (amount: U32.t { U32.v amount <= 8 })
: Tot (y: U8.t { U8.v y == U8.v x `U.shift_right` U32.v amount })
= let y =
      if amount = 8ul then 0uy else x `U8.shift_right` amount
  in
  y

// inline_for_extraction // no, because of https://github.com/FStarLang/kremlin/issues/102
let get_bitfield_gen8
  (x: U8.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 8})
: Tot (y: U8.t { U8.v y == get_bitfield (U8.v x) (U32.v lo) (U32.v hi) })
= get_bitfield_eq_2 #8 (U8.v x) (U32.v lo) (U32.v hi);
  (* NOTE: due to https://github.com/FStarLang/kremlin/issues/102 I need to introduce explicit let-bindings here *)
  let op1 = x `U8.shift_left` (8ul `U32.sub` hi) in
  let op2 = op1 `U8.shift_right` ((8ul `U32.sub` hi) `U32.add` lo) in
  op2

// inline_for_extraction // no, same
let set_bitfield_gen8
  (x: U8.t) (lo: U32.t) (hi: U32.t {U32.v lo < U32.v hi /\ U32.v hi <= 8})
  (v: U8.t { U8.v v < pow2 (U32.v hi - U32.v lo) })
: Tot (y: U8.t { U8.v y == set_bitfield (U8.v x) (U32.v lo) (U32.v hi) (U8.v v) })
= bitfield_mask_eq_2 8 (U32.v lo) (U32.v hi);
  (* NOTE: due to https://github.com/FStarLang/kremlin/issues/102 I need to introduce explicit let-bindings here *)
  let op0 = (U8.lognot 0uy) in
  let op1 = op0 `U8.shift_right` (8ul `U32.sub` (hi `U32.sub` lo)) in
  let op2 = op1 `U8.shift_left` lo in
  let op3 = U8.lognot op2 in
  let op4 = x `U8.logand` op3 in
  let op5 = v `U8.shift_left` lo in
  let op6 = op4 `U8.logor` op5 in
  op6

inline_for_extraction
let get_bitfield8
  (x: U8.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 8})
: Tot (y: U8.t { U8.v y == get_bitfield (U8.v x) lo hi })
= if lo = hi then 0uy else
  get_bitfield_gen8 x (U32.uint_to_t lo) (U32.uint_to_t hi)

inline_for_extraction
let not_bitfield_mask8 (lo: nat) (hi: nat { lo <= hi /\ hi <= 8 }) : Tot (x: U8.t { U8.v x == not_bitfield_mask 8 lo hi }) =
  U8.lognot (bitfield_mask8 lo hi)

inline_for_extraction
let u8_shift_left
  (x: U8.t)
  (amount: U32.t { U32.v amount <= 8 })
: Tot (y: U8.t { U8.v y == U8.v x `U.shift_left` U32.v amount })
= let y =
      if amount = 8ul then 0uy else x `U8.shift_left` amount
  in
  y

inline_for_extraction
let set_bitfield8
  (x: U8.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 8})
  (v: U8.t { U8.v v < pow2 (hi - lo) })
: Tot (y: U8.t { U8.v y == set_bitfield (U8.v x) lo hi (U8.v v) })
= if lo = hi then begin
    set_bitfield_empty #8 (U8.v x) lo (U8.v v);
    x
  end else set_bitfield_gen8 x (U32.uint_to_t lo) (U32.uint_to_t hi) v

inline_for_extraction
let bitfield_eq8_lhs
  (x: U8.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 8})
: Tot U8.t
= x `U8.logand` bitfield_mask8 lo hi

inline_for_extraction
let bitfield_eq8_rhs
  (x: U8.t) (lo: nat) (hi: nat {lo <= hi /\ hi <= 8})
  (v: U8.t { U8.v v < pow2 (hi - lo) })
: Tot (y: U8.t { bitfield_eq8_lhs x lo hi == y <==> (get_bitfield8 x lo hi <: U8.t) == v })
= [@inline_let] let _ =
    bitfield_eq_shift (U8.v x) lo hi (U8.v v)
  in
  v `u8_shift_left` U32.uint_to_t lo

inline_for_extraction
noextract
let uint64 : uint_t 64 U64.t = {
  v = U64.v;
  uint_to_t = U64.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield_gen = (fun x lo hi -> get_bitfield_gen64 x lo hi);
  set_bitfield_gen = (fun x lo hi z -> set_bitfield_gen64 x lo hi z);
  get_bitfield = (fun x lo hi -> get_bitfield64 x lo hi);
  set_bitfield = (fun x lo hi z -> set_bitfield64 x lo hi z);
  logor = (fun x y -> U64.logor x y);
  bitfield_eq_lhs = (fun x lo hi -> bitfield_eq64_lhs x lo hi);
  bitfield_eq_rhs = (fun x lo hi z -> bitfield_eq64_rhs x lo hi z);
}

let uint64_v_eq x = ()
let uint64_uint_to_t_eq x = ()

inline_for_extraction
noextract
let uint32 : uint_t 32 U32.t = {
  v = U32.v;
  uint_to_t = U32.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield_gen = (fun x lo hi -> get_bitfield_gen32 x lo hi);
  set_bitfield_gen = (fun x lo hi z -> set_bitfield_gen32 x lo hi z);
  get_bitfield = (fun x lo hi -> get_bitfield32 x lo hi);
  set_bitfield = (fun x lo hi z -> set_bitfield32 x lo hi z);
  logor = (fun x y -> U32.logor x y);
  bitfield_eq_lhs = (fun x lo hi -> bitfield_eq32_lhs x lo hi);
  bitfield_eq_rhs = (fun x lo hi z -> bitfield_eq32_rhs x lo hi z);
}

let uint32_v_eq x = ()
let uint32_uint_to_t_eq x = ()

inline_for_extraction
noextract
let uint16 : uint_t 16 U16.t = {
  v = U16.v;
  uint_to_t = U16.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield_gen = (fun x lo hi -> get_bitfield_gen16 x lo hi);
  set_bitfield_gen = (fun x lo hi z -> set_bitfield_gen16 x lo hi z);
  get_bitfield = (fun x lo hi -> get_bitfield16 x lo hi);
  set_bitfield = (fun x lo hi z -> set_bitfield16 x lo hi z);
  logor = (fun x y -> U16.logor x y);
  bitfield_eq_lhs = (fun x lo hi -> bitfield_eq16_lhs x lo hi);
  bitfield_eq_rhs = (fun x lo hi z -> bitfield_eq16_rhs x lo hi z);
}

let uint16_v_eq x = ()
let uint16_uint_to_t_eq x = ()

inline_for_extraction
noextract
let uint8 : uint_t 8 U8.t = {
  v = U8.v;
  uint_to_t = U8.uint_to_t;
  v_uint_to_t = (fun _ -> ());
  uint_to_t_v = (fun _ -> ());
  get_bitfield_gen = (fun x lo hi -> get_bitfield_gen8 x lo hi);
  set_bitfield_gen = (fun x lo hi z -> set_bitfield_gen8 x lo hi z);
  get_bitfield = (fun x lo hi -> get_bitfield8 x lo hi);
  set_bitfield = (fun x lo hi z -> set_bitfield8 x lo hi z);
  logor = (fun x y -> U8.logor x y);
  bitfield_eq_lhs = (fun x lo hi -> bitfield_eq8_lhs x lo hi);
  bitfield_eq_rhs = (fun x lo hi z -> bitfield_eq8_rhs x lo hi z);
}

let uint8_v_eq x = ()
let uint8_uint_to_t_eq x = ()
