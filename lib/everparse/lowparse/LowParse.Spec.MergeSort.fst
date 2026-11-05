module LowParse.Spec.MergeSort

(* Specification of a bottom-up merge sort over sequences, with abort
   on the first pair of elements comparing equal. Used by
   LowParse.Pulse.MergeSort. *)

module Seq = FStar.Seq
module SP = FStar.Seq.Properties

let compare_props (#t: Type) (cmp: t -> t -> int) : prop =
  (forall x y z . (cmp x y < 0 /\ cmp y z < 0) ==> cmp x z < 0) /\
  (forall x y . cmp x y < 0 <==> cmp y x > 0)

let same_sign (r: int) (c: int) : prop =
  (r < 0 <==> c < 0) /\ (r == 0 <==> c == 0)

let ssorted (#t: Type) (cmp: t -> t -> int) (s: Seq.seq t) : prop =
  forall (i: nat) . i + 1 < Seq.length s ==> cmp (Seq.index s i) (Seq.index s (i + 1)) < 0

let runs_sorted (#t: Type) (cmp: t -> t -> int) (w: pos) (s: Seq.seq t) : prop =
  forall (i: nat) . (i + 1 < Seq.length s /\ (i + 1) % w <> 0) ==> cmp (Seq.index s i) (Seq.index s (i + 1)) < 0

let rec smerge
  (#t: Type)
  (cmp: t -> t -> int)
  (s1 s2: Seq.seq t)
: Tot (bool & Seq.seq t)
  (decreases (Seq.length s1 + Seq.length s2))
= if Seq.length s1 = 0
  then (true, s2)
  else if Seq.length s2 = 0
  then (true, s1)
  else
    let x1 = Seq.head s1 in
    let x2 = Seq.head s2 in
    let c = cmp x1 x2 in
    if c = 0
    then (false, Seq.append s1 s2)
    else if c < 0
    then
      let (b, r) = smerge cmp (Seq.tail s1) s2 in
      (b, Seq.cons x1 r)
    else
      let (b, r) = smerge cmp s1 (Seq.tail s2) in
      (b, Seq.cons x2 r)

let count_cons (#t: eqtype) (x a: t) (s: Seq.seq t) : Lemma
  (SP.count x (Seq.cons a s) == (if a = x then 1 else 0) + SP.count x s)
= let s' = Seq.cons a s in
  assert (Seq.head s' == a);
  assert (Seq.tail s' `Seq.equal` s)

let count_head_tail (#t: eqtype) (x: t) (s: Seq.seq t) : Lemma
  (requires Seq.length s > 0)
  (ensures SP.count x s == (if Seq.head s = x then 1 else 0) + SP.count x (Seq.tail s))
= ()

#push-options "--z3rlimit 32"

let rec smerge_count
  (#t: eqtype)
  (cmp: t -> t -> int)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures (
    let (_, r) = smerge cmp s1 s2 in
    Seq.length r == Seq.length s1 + Seq.length s2 /\
    (forall x . SP.count x r == SP.count x s1 + SP.count x s2)
  ))
  (decreases (Seq.length s1 + Seq.length s2))
= SP.lemma_append_count s1 s2;
  if Seq.length s1 = 0
  then ()
  else if Seq.length s2 = 0
  then ()
  else
    let x1 = Seq.head s1 in
    let x2 = Seq.head s2 in
    let c = cmp x1 x2 in
    if c = 0
    then ()
    else if c < 0
    then begin
      smerge_count cmp (Seq.tail s1) s2;
      let (_, r) = smerge cmp (Seq.tail s1) s2 in
      Classical.forall_intro (fun x -> count_cons x x1 r);
      Classical.forall_intro (fun x -> count_head_tail x s1)
    end else begin
      smerge_count cmp s1 (Seq.tail s2);
      let (_, r) = smerge cmp s1 (Seq.tail s2) in
      Classical.forall_intro (fun x -> count_cons x x2 r);
      Classical.forall_intro (fun x -> count_head_tail x s2)
    end

let ssorted_tail (#t: Type) (cmp: t -> t -> int) (s: Seq.seq t) : Lemma
  (requires ssorted cmp s /\ Seq.length s > 0)
  (ensures ssorted cmp (Seq.tail s))
= let s' = Seq.tail s in
  assert (forall (i: nat) . i < Seq.length s' ==> Seq.index s' i == Seq.index s (i + 1))

let ssorted_cons (#t: Type) (cmp: t -> t -> int) (x: t) (s: Seq.seq t) : Lemma
  (requires ssorted cmp s /\ (Seq.length s > 0 ==> cmp x (Seq.head s) < 0))
  (ensures ssorted cmp (Seq.cons x s))
= let s' = Seq.cons x s in
  assert (forall (i: nat) . i < Seq.length s ==> Seq.index s' (i + 1) == Seq.index s i);
  assert (Seq.index s' 0 == x)

let rec smerge_sorted
  (#t: Type)
  (cmp: t -> t -> int)
  (s1 s2: Seq.seq t)
: Lemma
  (requires compare_props cmp /\ ssorted cmp s1 /\ ssorted cmp s2)
  (ensures (
    let (b, r) = smerge cmp s1 s2 in
    b == true ==> (
      ssorted cmp r /\
      (Seq.length r > 0 ==> (
        (Seq.length s1 > 0 /\ Seq.head r == Seq.head s1) \/
        (Seq.length s2 > 0 /\ Seq.head r == Seq.head s2)
      ))
    )
  ))
  (decreases (Seq.length s1 + Seq.length s2))
= if Seq.length s1 = 0
  then ()
  else if Seq.length s2 = 0
  then ()
  else
    let x1 = Seq.head s1 in
    let x2 = Seq.head s2 in
    let c = cmp x1 x2 in
    if c = 0
    then ()
    else if c < 0
    then begin
      ssorted_tail cmp s1;
      smerge_sorted cmp (Seq.tail s1) s2;
      let (b, r) = smerge cmp (Seq.tail s1) s2 in
      if b
      then begin
        if Seq.length (Seq.tail s1) > 0
        then assert (Seq.head (Seq.tail s1) == Seq.index s1 1)
        else ();
        ssorted_cons cmp x1 r
      end
      else ()
    end else begin
      ssorted_tail cmp s2;
      smerge_sorted cmp s1 (Seq.tail s2);
      let (b, r) = smerge cmp s1 (Seq.tail s2) in
      if b
      then begin
        if Seq.length (Seq.tail s2) > 0
        then assert (Seq.head (Seq.tail s2) == Seq.index s2 1)
        else ();
        ssorted_cons cmp x2 r
      end
      else ()
    end

let rec smerge_abort
  (#t: eqtype)
  (cmp: t -> t -> int)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures (
    let (b, _) = smerge cmp s1 s2 in
    b == false ==> (exists x1 x2 . SP.mem x1 s1 /\ SP.mem x2 s2 /\ cmp x1 x2 == 0)
  ))
  (decreases (Seq.length s1 + Seq.length s2))
= if Seq.length s1 = 0
  then ()
  else if Seq.length s2 = 0
  then ()
  else
    let x1 = Seq.head s1 in
    let x2 = Seq.head s2 in
    let c = cmp x1 x2 in
    if c = 0
    then begin
      count_head_tail x1 s1;
      count_head_tail x2 s2
    end
    else if c < 0
    then begin
      smerge_abort cmp (Seq.tail s1) s2;
      Classical.forall_intro (fun x -> count_head_tail x s1)
    end else begin
      smerge_abort cmp s1 (Seq.tail s2);
      Classical.forall_intro (fun x -> count_head_tail x s2)
    end

#pop-options

(* One step of the merge loop *)

let smerge_step
  (#t: Type)
  (cmp: t -> t -> int)
  (s1 s2: Seq.seq t)
: Lemma
  (requires Seq.length s1 > 0 \/ Seq.length s2 > 0)
  (ensures (
    let (b, r) = smerge cmp s1 s2 in
    if Seq.length s1 = 0
    then b == true /\ r == s2
    else if Seq.length s2 = 0
    then b == true /\ r == s1
    else begin
      let c = cmp (Seq.head s1) (Seq.head s2) in
      if c = 0
      then b == false
      else if c < 0
      then (b, r) == (fst (smerge cmp (Seq.tail s1) s2), Seq.cons (Seq.head s1) (snd (smerge cmp (Seq.tail s1) s2)))
      else (b, r) == (fst (smerge cmp s1 (Seq.tail s2)), Seq.cons (Seq.head s2) (snd (smerge cmp s1 (Seq.tail s2))))
    end
  ))
= ()

let smerge_empty
  (#t: Type)
  (cmp: t -> t -> int)
: Lemma
  (smerge cmp Seq.empty Seq.empty == (true, Seq.empty))
= ()

(* Relating runs and sortedness *)

#push-options "--z3rlimit 32"

let runs_sorted_one (#t: Type) (cmp: t -> t -> int) (s: Seq.seq t) : Lemma
  (runs_sorted cmp 1 s)
= ()

let runs_sorted_full (#t: Type) (cmp: t -> t -> int) (w: pos) (s: Seq.seq t) : Lemma
  (requires runs_sorted cmp w s /\ Seq.length s <= w)
  (ensures ssorted cmp s)
= let prf (i: nat) : Lemma
    (requires i + 1 < Seq.length s)
    (ensures (i + 1) % w <> 0)
  = FStar.Math.Lemmas.small_mod (i + 1) w
  in
  Classical.forall_intro (Classical.move_requires prf)

let runs_sorted_slice
  (#t: Type) (cmp: t -> t -> int) (w: pos) (s: Seq.seq t) (lo hi: nat)
: Lemma
  (requires runs_sorted cmp w s /\ lo % w == 0 /\ lo <= hi /\ hi <= Seq.length s /\ hi <= lo + w)
  (ensures ssorted cmp (Seq.slice s lo hi))
= let s' = Seq.slice s lo hi in
  let prf (i: nat) : Lemma
    (requires i + 1 < hi - lo)
    (ensures i + 1 < Seq.length s' /\ cmp (Seq.index s' i) (Seq.index s' (i + 1)) < 0)
  = FStar.Math.Lemmas.lemma_mod_plus (i + 1) (lo / w) w;
    FStar.Math.Lemmas.small_mod (i + 1) w;
    FStar.Math.Lemmas.euclidean_division_definition lo w;
    assert ((lo + i + 1) % w == (i + 1) % w)
  in
  Classical.forall_intro (Classical.move_requires prf)

let mod_double (lo: nat) (w: pos) : Lemma
  (requires lo % (2 * w) == 0)
  (ensures lo % w == 0 /\ (lo + w) % w == 0)
= FStar.Math.Lemmas.euclidean_division_definition lo (2 * w);
  FStar.Math.Lemmas.paren_mul_right (lo / (2 * w)) 2 w;
  FStar.Math.Lemmas.cancel_mul_mod ((lo / (2 * w)) * 2) w;
  FStar.Math.Lemmas.lemma_mod_plus lo 1 w

let mod_next (lo: nat) (w: pos) : Lemma
  (requires lo % (2 * w) == 0)
  (ensures (lo + 2 * w) % (2 * w) == 0)
= FStar.Math.Lemmas.lemma_mod_plus lo 1 (2 * w)

let runs_sorted_extend
  (#t: Type) (cmp: t -> t -> int) (w: pos) (s: Seq.seq t) (lo hi: nat)
: Lemma
  (requires
    lo <= hi /\ hi <= Seq.length s /\
    lo % w == 0 /\
    runs_sorted cmp w (Seq.slice s 0 lo) /\
    ssorted cmp (Seq.slice s lo hi)
  )
  (ensures runs_sorted cmp w (Seq.slice s 0 hi))
= let s1 = Seq.slice s 0 lo in
  let s2 = Seq.slice s lo hi in
  let s' = Seq.slice s 0 hi in
  let prf (i: nat) : Lemma
    (requires i + 1 < hi /\ (i + 1) % w <> 0)
    (ensures i + 1 < Seq.length s' /\ cmp (Seq.index s' i) (Seq.index s' (i + 1)) < 0)
  = if i + 1 < lo
    then assert (Seq.index s1 i == Seq.index s' i /\ Seq.index s1 (i + 1) == Seq.index s' (i + 1))
    else if i + 1 = lo
    then ()
    else assert (Seq.index s2 (i - lo) == Seq.index s' i /\ Seq.index s2 (i - lo + 1) == Seq.index s' (i + 1))
  in
  Classical.forall_intro (Classical.move_requires prf)

#pop-options

(* Permutations and the abort witness *)

let count_slice3 (#t: eqtype) (s: Seq.seq t) (lo mid hi: nat) (x: t) : Lemma
  (requires lo <= mid /\ mid <= hi /\ hi <= Seq.length s)
  (ensures SP.count x (Seq.slice s lo hi) == SP.count x (Seq.slice s lo mid) + SP.count x (Seq.slice s mid hi))
= let s' = Seq.slice s lo hi in
  SP.lemma_count_slice s' (mid - lo);
  assert (Seq.slice s' 0 (mid - lo) `Seq.equal` Seq.slice s lo mid);
  assert (Seq.slice s' (mid - lo) (Seq.length s') `Seq.equal` Seq.slice s mid hi)

let count_full_slice (#t: eqtype) (s: Seq.seq t) (x: t) : Lemma
  (SP.count x (Seq.slice s 0 (Seq.length s)) == SP.count x s)
= assert (Seq.slice s 0 (Seq.length s) `Seq.equal` s)

let sort_abort_witness (#t: eqtype) (cmp: t -> t -> int) (s0: Seq.seq t) : prop =
  exists x1 x2 . SP.mem x1 s0 /\ SP.mem x2 s0 /\ cmp x1 x2 == 0 /\ (x1 <> x2 \/ SP.count x1 s0 >= 2)

let abort_witness_lift
  (#t: eqtype) (cmp: t -> t -> int) (s0 s: Seq.seq t) (lo mid hi: nat)
: Lemma
  (requires
    lo <= mid /\ mid <= hi /\ hi <= Seq.length s /\
    SP.permutation t s0 s /\
    (exists x1 x2 . SP.mem x1 (Seq.slice s lo mid) /\ SP.mem x2 (Seq.slice s mid hi) /\ cmp x1 x2 == 0)
  )
  (ensures sort_abort_witness cmp s0)
= let prf (x1 x2: t) : Lemma
    (requires SP.mem x1 (Seq.slice s lo mid) /\ SP.mem x2 (Seq.slice s mid hi) /\ cmp x1 x2 == 0)
    (ensures sort_abort_witness cmp s0)
  = let f (x: t) : Lemma
      (SP.count x s >= SP.count x (Seq.slice s lo mid) + SP.count x (Seq.slice s mid hi))
    = count_slice3 s lo mid hi x;
      count_slice3 s 0 lo hi x;
      count_slice3 s 0 hi (Seq.length s) x;
      count_full_slice s x
    in
    f x1; f x2
  in
  Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (prf x1) x2)

let sort_post (#t: eqtype) (cmp: t -> t -> int) (s0 s1: Seq.seq t) (res: bool) : prop =
  Seq.length s1 == Seq.length s0 /\
  SP.permutation t s0 s1 /\
  (res == true ==> ssorted cmp s1) /\
  (res == false ==> sort_abort_witness cmp s0)

(* Consequences for clients *)

let rec ssorted_lt
  (#t: Type) (cmp: t -> t -> int) (s: Seq.seq t) (i j: nat)
: Lemma
  (requires compare_props cmp /\ ssorted cmp s /\ i < j /\ j < Seq.length s)
  (ensures cmp (Seq.index s i) (Seq.index s j) < 0)
  (decreases (j - i))
= if j = i + 1
  then ()
  else ssorted_lt cmp s i (j - 1)

let rec count2_indices (#t: eqtype) (x: t) (s: Seq.seq t) : Ghost (nat & nat)
  (requires SP.count x s >= 2)
  (ensures fun (i, j) -> i < j /\ j < Seq.length s /\ Seq.index s i == x /\ Seq.index s j == x)
  (decreases (Seq.length s))
= if Seq.head s = x
  then begin
    let k = SP.index_mem x (Seq.tail s) in
    (0, k + 1)
  end else begin
    let (i, j) = count2_indices x (Seq.tail s) in
    (i + 1, j + 1)
  end

let sorted_no_dup
  (#t: eqtype) (cmp: t -> t -> int) (s0 s1: Seq.seq t)
: Lemma
  (requires compare_props cmp /\ ssorted cmp s1 /\ SP.permutation t s0 s1)
  (ensures ~ (sort_abort_witness cmp s0))
= let prf (x1 x2: t) : Lemma
    (requires SP.mem x1 s0 /\ SP.mem x2 s0 /\ cmp x1 x2 == 0 /\ (x1 <> x2 \/ SP.count x1 s0 >= 2))
    (ensures False)
  = let i = SP.index_mem x1 s1 in
    let j = SP.index_mem x2 s1 in
    if x1 <> x2
    then begin
      if i < j then ssorted_lt cmp s1 i j
      else ssorted_lt cmp s1 j i
    end else begin
      let (i', j') = count2_indices x1 s1 in
      ssorted_lt cmp s1 i' j'
    end
  in
  Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (prf x1) x2)

(* When the sorted elements are pairwise distinct (e.g. offsets), the
   abort witness is exactly a pair of positions comparing equal. *)

let seq_distinct (#t: eqtype) (s: Seq.seq t) : prop =
  forall (i j: nat) . (i < j /\ j < Seq.length s) ==> Seq.index s i <> Seq.index s j

let seq_no_cmp_dup (#t: Type) (cmp: t -> t -> int) (s: Seq.seq t) : prop =
  forall (i j: nat) . (i < j /\ j < Seq.length s) ==> cmp (Seq.index s i) (Seq.index s j) <> 0

let sort_abort_witness_distinct
  (#t: eqtype) (cmp: t -> t -> int) (s: Seq.seq t)
: Lemma
  (requires compare_props cmp /\ seq_distinct s)
  (ensures sort_abort_witness cmp s <==> ~ (seq_no_cmp_dup cmp s))
= let prf1 (x1 x2: t) : Lemma
    (requires SP.mem x1 s /\ SP.mem x2 s /\ cmp x1 x2 == 0 /\ (x1 <> x2 \/ SP.count x1 s >= 2))
    (ensures ~ (seq_no_cmp_dup cmp s))
  = if x1 <> x2
    then begin
      let i = SP.index_mem x1 s in
      let j = SP.index_mem x2 s in
      assert (i <> j);
      if i < j then () else assert (cmp (Seq.index s j) (Seq.index s i) == 0)
    end else begin
      let (i, j) = count2_indices x1 s in
      assert (Seq.index s i == Seq.index s j)
    end
  in
  let prf2 (i j: nat) : Lemma
    (requires i < j /\ j < Seq.length s /\ cmp (Seq.index s i) (Seq.index s j) == 0)
    (ensures sort_abort_witness cmp s)
  = assert (SP.mem (Seq.index s i) s);
    assert (SP.mem (Seq.index s j) s)
  in
  Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (prf1 x1) x2);
  Classical.forall_intro_2 (fun i j -> Classical.move_requires (prf2 i) j)
