module LowParse.Pulse.MergeSort
#lang-pulse
include LowParse.Spec.MergeSort
open Pulse.Lib.Pervasives

(* A bottom-up merge sort over a slice, using a caller-provided scratch
   slice of the same length, with loops only (no recursion), aborting on
   the first pair of elements comparing equal. Meant to be inlined, so
   that the comparison function need not be a closure. *)

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module I16 = FStar.Int16
module Seq = FStar.Seq
module SP = FStar.Seq.Properties

inline_for_extraction
let impl_cmp_t
  (#t: Type0)
  (inv: slprop)
  (pre: t -> prop)
  (cmp: Ghost.erased (t -> t -> int))
=
  (x: t) ->
  (y: t) ->
  stt I16.t
    (inv ** pure (pre x /\ pre y))
    (fun r -> inv ** pure (same_sign (I16.v r) (Ghost.reveal cmp x y)))

let seq_pre (#t: eqtype) (pre: t -> prop) (s: Seq.seq t) : prop =
  forall x . SP.mem x s ==> pre x

let rec index_mem (#t: eqtype) (s: Seq.seq t) (i: nat) : Lemma
  (requires i < Seq.length s)
  (ensures SP.mem (Seq.index s i) s)
  (decreases i)
= if i = 0
  then ()
  else index_mem (Seq.tail s) (i - 1)

let seq_pre_index (#t: eqtype) (pre: t -> prop) (s: Seq.seq t) (i: nat) : Lemma
  (requires seq_pre pre s /\ i < Seq.length s)
  (ensures pre (Seq.index s i))
= index_mem s i

(* Merge *)

let merge_inv
  (#t: Type)
  (cmp: t -> t -> int)
  (sa st0 st: Seq.seq t)
  (lo mid hi i1 i2 k: nat)
  (ok: bool)
: Tot prop
= lo <= i1 /\ i1 <= mid /\ mid <= i2 /\ i2 <= hi /\ hi <= Seq.length sa /\
  Seq.length st == Seq.length sa /\ Seq.length st0 == Seq.length sa /\
  k == lo + (i1 - lo) + (i2 - mid) /\
  Seq.slice st 0 lo == Seq.slice st0 0 lo /\
  (let r0 = smerge cmp (Seq.slice sa lo mid) (Seq.slice sa mid hi) in
   if ok
   then begin
     let r = smerge cmp (Seq.slice sa i1 mid) (Seq.slice sa i2 hi) in
     fst r0 == fst r /\
     (fst r0 == true ==> snd r0 == Seq.append (Seq.slice st lo k) (snd r))
   end
   else fst r0 == false
  )

let merge_post
  (#t: Type)
  (cmp: t -> t -> int)
  (sa st0 st: Seq.seq t)
  (lo mid hi: nat)
  (res: bool)
: Tot prop
= lo <= mid /\ mid <= hi /\ hi <= Seq.length sa /\
  Seq.length st == Seq.length sa /\ Seq.length st0 == Seq.length sa /\
  Seq.slice st 0 lo == Seq.slice st0 0 lo /\
  (let r0 = smerge cmp (Seq.slice sa lo mid) (Seq.slice sa mid hi) in
    res == fst r0 /\
    (res == true ==> Seq.slice st lo hi == snd r0)
  )

let merge_inv_intro
  (#t: Type)
  (cmp: t -> t -> int)
  (sa st0: Seq.seq t)
  (lo mid hi: nat)
: Lemma
  (requires lo <= mid /\ mid <= hi /\ hi <= Seq.length sa /\ Seq.length st0 == Seq.length sa)
  (ensures merge_inv cmp sa st0 st0 lo mid hi lo mid lo true)
= assert (Seq.slice st0 lo lo `Seq.equal` Seq.empty);
  Seq.append_empty_l (snd (smerge cmp (Seq.slice sa lo mid) (Seq.slice sa mid hi)))

let slice_cons (#t: Type) (s: Seq.seq t) (i j: nat) : Lemma
  (requires i < j /\ j <= Seq.length s)
  (ensures
    Seq.length (Seq.slice s i j) > 0 /\
    Seq.head (Seq.slice s i j) == Seq.index s i /\
    Seq.tail (Seq.slice s i j) == Seq.slice s (i + 1) j
  )
= assert (Seq.tail (Seq.slice s i j) `Seq.equal` Seq.slice s (i + 1) j)

#push-options "--z3rlimit 64"

let merge_inv_take
  (#t: Type)
  (cmp: t -> t -> int)
  (sa st0 st: Seq.seq t)
  (lo mid hi i1 i2 k: nat)
  (left: bool)
: Lemma
  (requires
    merge_inv cmp sa st0 st lo mid hi i1 i2 k true /\
    (if left
     then i1 < mid /\ (i2 == hi \/ cmp (Seq.index sa i1) (Seq.index sa i2) < 0)
     else i2 < hi /\ (i1 == mid \/ (cmp (Seq.index sa i1) (Seq.index sa i2) <> 0 /\ ~ (cmp (Seq.index sa i1) (Seq.index sa i2) < 0)))
    )
  )
  (ensures (
    let x = if left then Seq.index sa i1 else Seq.index sa i2 in
    k < Seq.length st /\
    merge_inv cmp sa st0 (Seq.upd st k x) lo mid hi (if left then i1 + 1 else i1) (if left then i2 else i2 + 1) (k + 1) true
  ))
= let x = if left then Seq.index sa i1 else Seq.index sa i2 in
  let s1 = Seq.slice sa i1 mid in
  let s2 = Seq.slice sa i2 hi in
  if i1 < mid then slice_cons sa i1 mid;
  if i2 < hi then slice_cons sa i2 hi;
  smerge_step cmp s1 s2;
  let st' = Seq.upd st k x in
  assert (Seq.slice st' 0 lo `Seq.equal` Seq.slice st 0 lo);
  assert (Seq.slice st' lo (k + 1) `Seq.equal` Seq.append (Seq.slice st lo k) (Seq.create 1 x));
  let r = smerge cmp (if left then Seq.tail s1 else s1) (if left then s2 else Seq.tail s2) in
  Seq.append_assoc (Seq.slice st lo k) (Seq.create 1 x) (snd r);
  assert (Seq.cons x (snd r) == Seq.append (Seq.create 1 x) (snd r))

let merge_inv_abort
  (#t: Type)
  (cmp: t -> t -> int)
  (sa st0 st: Seq.seq t)
  (lo mid hi i1 i2 k: nat)
: Lemma
  (requires
    merge_inv cmp sa st0 st lo mid hi i1 i2 k true /\
    i1 < mid /\ i2 < hi /\ cmp (Seq.index sa i1) (Seq.index sa i2) == 0
  )
  (ensures (
    merge_inv cmp sa st0 st lo mid hi i1 i2 k false
  ))
= slice_cons sa i1 mid;
  slice_cons sa i2 hi;
  smerge_step cmp (Seq.slice sa i1 mid) (Seq.slice sa i2 hi)

let merge_inv_end
  (#t: Type)
  (cmp: t -> t -> int)
  (sa st0 st: Seq.seq t)
  (lo mid hi i1 i2 k: nat)
  (ok: bool)
: Lemma
  (requires
    merge_inv cmp sa st0 st lo mid hi i1 i2 k ok /\
    (ok == true ==> (i1 == mid /\ i2 == hi))
  )
  (ensures (
    merge_post cmp sa st0 st lo mid hi ok
  ))
= if ok
  then begin
    assert (Seq.slice sa i1 mid `Seq.equal` Seq.empty);
    assert (Seq.slice sa i2 hi `Seq.equal` Seq.empty);
    smerge_empty cmp;
    Seq.append_empty_r (Seq.slice st lo k)
  end
  else ()

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
fn merge
  (#t: eqtype)
  (#inv: slprop)
  (#pre: Ghost.erased (t -> prop))
  (#cmp: Ghost.erased (t -> t -> int))
  (impl_cmp: impl_cmp_t inv pre cmp)
  (a: S.slice t)
  (tmp: S.slice t)
  (lo mid hi: SZ.t)
  (#pa: perm)
  (#sa: Ghost.erased (Seq.seq t))
  (#st0: Ghost.erased (Seq.seq t))
requires
  inv ** pts_to a #pa sa ** pts_to tmp st0 **
  pure (
    SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ SZ.v hi <= Seq.length sa /\
    Seq.length st0 == Seq.length sa /\
    seq_pre pre sa
  )
returns res: bool
ensures exists* st .
  inv ** pts_to a #pa sa ** pts_to tmp st **
  pure (merge_post cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) res)
{
  let mut pi1 = lo;
  let mut pi2 = mid;
  let mut pk = lo;
  let mut pok = true;
  merge_inv_intro cmp sa st0 (SZ.v lo) (SZ.v mid) (SZ.v hi);
  while (
    let ok = !pok;
    let i1 = !pi1;
    let i2 = !pi2;
    (ok && (i1 <> mid || i2 <> hi))
  )
  invariant exists* i1 i2 k ok st .
    inv ** pts_to a #pa sa ** pts_to tmp st **
    pts_to pi1 i1 ** pts_to pi2 i2 ** pts_to pk k ** pts_to pok ok **
    pure (merge_inv cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k) ok)
  decreases ((SZ.v mid - SZ.v !pi1) + (SZ.v hi - SZ.v !pi2) + (if !pok then 1 else 0))
  {
    let i1 = !pi1;
    let i2 = !pi2;
    let k = !pk;
    with st . assert (pts_to tmp st);
    S.pts_to_len tmp;
    if (i1 = mid) {
      let x = S.op_Dot_Lparen_Rparen a i2;
      merge_inv_take cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k) false;
      S.op_Dot_Lparen_Rparen_Less_Minus tmp k x;
      pi2 := SZ.add i2 1sz;
      pk := SZ.add k 1sz;
    } else if (i2 = hi) {
      let x = S.op_Dot_Lparen_Rparen a i1;
      merge_inv_take cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k) true;
      S.op_Dot_Lparen_Rparen_Less_Minus tmp k x;
      pi1 := SZ.add i1 1sz;
      pk := SZ.add k 1sz;
    } else {
      let x1 = S.op_Dot_Lparen_Rparen a i1;
      let x2 = S.op_Dot_Lparen_Rparen a i2;
      seq_pre_index pre sa (SZ.v i1);
      seq_pre_index pre sa (SZ.v i2);
      let c = impl_cmp x1 x2;
      if (c = 0s) {
        merge_inv_abort cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k);
        pok := false;
      } else if (I16.lt c 0s) {
        merge_inv_take cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k) true;
        S.op_Dot_Lparen_Rparen_Less_Minus tmp k x1;
        pi1 := SZ.add i1 1sz;
        pk := SZ.add k 1sz;
      } else {
        merge_inv_take cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k) false;
        S.op_Dot_Lparen_Rparen_Less_Minus tmp k x2;
        pi2 := SZ.add i2 1sz;
        pk := SZ.add k 1sz;
      }
    }
  };
  let ok = !pok;
  with st i1 i2 k . assert (pts_to tmp st ** pts_to pi1 i1 ** pts_to pi2 i2 ** pts_to pk k);
  merge_inv_end cmp sa st0 st (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v i1) (SZ.v i2) (SZ.v k) ok;
  ok
}

#pop-options

(* One pass: merge adjacent runs of width w from a into tmp *)

let pass_inv
  (#t: eqtype)
  (cmp: t -> t -> int)
  (w: pos)
  (sa st: Seq.seq t)
  (lo: nat)
: Tot prop
= lo <= Seq.length sa /\
  Seq.length st == Seq.length sa /\
  (lo < Seq.length sa ==> lo % (2 * w) == 0) /\
  SP.permutation t (Seq.slice sa 0 lo) (Seq.slice st 0 lo) /\
  runs_sorted cmp (2 * w) (Seq.slice st 0 lo)

let pass_inv_intro
  (#t: eqtype)
  (cmp: t -> t -> int)
  (w: pos)
  (sa st: Seq.seq t)
: Lemma
  (requires Seq.length st == Seq.length sa)
  (ensures pass_inv cmp w sa st 0)
= runs_sorted_one cmp (Seq.slice st 0 0);
  assert (runs_sorted cmp (2 * w) (Seq.slice st 0 0))

let seq_pre_perm (#t: eqtype) (pre: t -> prop) (s1 s2: Seq.seq t) : Lemma
  (requires seq_pre pre s1 /\ SP.permutation t s1 s2)
  (ensures seq_pre pre s2)
= ()

let perm_trans (#t: eqtype) (s1 s2 s3: Seq.seq t) : Lemma
  (requires SP.permutation t s1 s2 /\ SP.permutation t s2 s3)
  (ensures SP.permutation t s1 s3)
= ()

#push-options "--z3rlimit 128"

let pass_step
  (#t: eqtype)
  (cmp: t -> t -> int)
  (w: pos)
  (s0 sa st0 st: Seq.seq t)
  (lo mid hi: nat)
  (res: bool)
: Lemma
  (requires
    compare_props cmp /\
    runs_sorted cmp w sa /\
    SP.permutation t s0 sa /\
    pass_inv cmp w sa st0 lo /\
    lo < Seq.length sa /\
    mid == (if w <= Seq.length sa - lo then lo + w else Seq.length sa) /\
    hi == (if w <= Seq.length sa - mid then mid + w else Seq.length sa) /\
    merge_post cmp sa st0 st lo mid hi res
  )
  (ensures
    (res == true ==> pass_inv cmp w sa st hi) /\
    (res == false ==> sort_abort_witness cmp s0)
  )
= let n = Seq.length sa in
  let s1 = Seq.slice sa lo mid in
  let s2 = Seq.slice sa mid hi in
  mod_double lo w;
  smerge_abort cmp s1 s2;
  smerge_count cmp s1 s2;
  if res
  then begin
    runs_sorted_slice cmp w sa lo mid;
    if mid < hi then runs_sorted_slice cmp w sa mid hi
    else assert (Seq.length s2 == 0);
    smerge_sorted cmp s1 s2;
    assert (Seq.slice st 0 lo == Seq.slice st0 0 lo);
    runs_sorted_extend cmp (2 * w) st lo hi;
    let f (x: t) : Lemma
      (SP.count x (Seq.slice sa 0 hi) == SP.count x (Seq.slice st 0 hi))
    = count_slice3 sa 0 lo hi x;
      count_slice3 sa lo mid hi x;
      count_slice3 st 0 lo hi x
    in
    Classical.forall_intro f;
    if hi < n then mod_next lo w
  end
  else abort_witness_lift cmp s0 sa lo mid hi

#pop-options

let pass_end
  (#t: eqtype)
  (cmp: t -> t -> int)
  (w: pos)
  (sa st: Seq.seq t)
: Lemma
  (requires pass_inv cmp w sa st (Seq.length sa))
  (ensures SP.permutation t sa st /\ runs_sorted cmp (2 * w) st)
= assert (Seq.slice sa 0 (Seq.length sa) `Seq.equal` sa);
  assert (Seq.slice st 0 (Seq.length sa) `Seq.equal` st)

#push-options "--z3rlimit 64"

inline_for_extraction
fn merge_pass
  (#t: eqtype)
  (#inv: slprop)
  (#pre: Ghost.erased (t -> prop))
  (#cmp: Ghost.erased (t -> t -> int))
  (impl_cmp: impl_cmp_t inv pre cmp)
  (a: S.slice t)
  (tmp: S.slice t)
  (w: SZ.t)
  (#pa: perm)
  (#s0: Ghost.erased (Seq.seq t))
  (#sa: Ghost.erased (Seq.seq t))
  (#st0: Ghost.erased (Seq.seq t))
requires
  inv ** pts_to a #pa sa ** pts_to tmp st0 **
  pure (
    SZ.v w > 0 /\
    Seq.length st0 == Seq.length sa /\
    compare_props cmp /\
    runs_sorted cmp (SZ.v w) sa /\
    SP.permutation t s0 sa /\
    seq_pre pre sa
  )
returns res: bool
ensures exists* st .
  inv ** pts_to a #pa sa ** pts_to tmp st **
  pure (
    SZ.v w > 0 /\
    Seq.length st == Seq.length sa /\
    (res == true ==> (SP.permutation t sa st /\ runs_sorted cmp (2 * SZ.v w) st)) /\
    (res == false ==> sort_abort_witness cmp s0)
  )
{
  S.pts_to_len a;
  let n = S.len a;
  let mut plo = 0sz;
  let mut pok = true;
  pass_inv_intro cmp (SZ.v w) sa st0;
  while (
    let ok = !pok;
    let lo = !plo;
    (ok && SZ.lt lo n)
  )
  invariant exists* lo ok st .
    inv ** pts_to a #pa sa ** pts_to tmp st **
    pts_to plo lo ** pts_to pok ok **
    pure (
      Seq.length st == Seq.length sa /\
      (ok == true ==> pass_inv cmp (SZ.v w) sa st (SZ.v lo)) /\
      (ok == false ==> sort_abort_witness cmp s0)
    )
  decreases ((SZ.v n - SZ.v !plo) + (if !pok then 1 else 0))
  {
    let lo = !plo;
    with st . assert (pts_to tmp st);
    let mid = (if SZ.lte w (SZ.sub n lo) then SZ.add lo w else n);
    let hi = (if SZ.lte w (SZ.sub n mid) then SZ.add mid w else n);
    let res = merge impl_cmp a tmp lo mid hi;
    with st' . assert (pts_to tmp st');
    pass_step cmp (SZ.v w) s0 sa st st' (SZ.v lo) (SZ.v mid) (SZ.v hi) res;
    if res {
      plo := hi;
    } else {
      pok := false;
    }
  };
  let ok = !pok;
  with st lo . assert (pts_to tmp st ** pts_to plo lo);
  if ok {
    pass_end cmp (SZ.v w) sa st;
    ()
  };
  ok
}

(* The sort *)

let sort_inv
  (#t: eqtype)
  (cmp: t -> t -> int)
  (s0 s: Seq.seq t)
  (w: nat)
  (ok done: bool)
: Tot prop
= Seq.length s == Seq.length s0 /\
  SP.permutation t s0 s /\
  (ok == true ==> (
    if done
    then ssorted cmp s
    else (w > 0 /\ w < Seq.length s /\ runs_sorted cmp w s)
  )) /\
  (ok == false ==> sort_abort_witness cmp s0)

let sort_inv_intro
  (#t: eqtype)
  (cmp: t -> t -> int)
  (s0: Seq.seq t)
: Lemma
  (sort_inv cmp s0 s0 1 true (Seq.length s0 <= 1))
= runs_sorted_one cmp s0;
  if Seq.length s0 <= 1 then runs_sorted_full cmp 1 s0

let sort_inv_end
  (#t: eqtype)
  (cmp: t -> t -> int)
  (s0 s: Seq.seq t)
  (w: nat)
  (ok done: bool)
: Lemma
  (requires sort_inv cmp s0 s w ok done /\ (ok == true ==> done == true))
  (ensures sort_post cmp s0 s ok)
= ()

inline_for_extraction
fn sort
  (#t: eqtype)
  (#inv: slprop)
  (#pre: Ghost.erased (t -> prop))
  (#cmp: Ghost.erased (t -> t -> int))
  (impl_cmp: impl_cmp_t inv pre cmp)
  (a: S.slice t)
  (tmp: S.slice t)
  (#s0: Ghost.erased (Seq.seq t))
  (#st0: Ghost.erased (Seq.seq t))
requires
  inv ** pts_to a s0 ** pts_to tmp st0 **
  pure (
    Seq.length st0 == Seq.length s0 /\
    compare_props cmp /\
    seq_pre pre s0
  )
returns res: bool
ensures exists* s1 st .
  inv ** pts_to a s1 ** pts_to tmp st **
  pure (sort_post cmp s0 s1 res)
{
  S.pts_to_len a;
  S.pts_to_len tmp;
  let n = S.len a;
  let mut pw = 1sz;
  let mut pok = true;
  let mut pdone = SZ.lte n 1sz;
  sort_inv_intro cmp s0;
  while (
    let ok = !pok;
    let done = !pdone;
    (ok && not done)
  )
  invariant exists* w ok done s st .
    inv ** pts_to a s ** pts_to tmp st **
    pts_to pw w ** pts_to pok ok ** pts_to pdone done **
    pure (
      Seq.length st == Seq.length s0 /\
      sort_inv cmp s0 s (SZ.v w) ok done
    )
  decreases (if !pok && not !pdone then SZ.v n - SZ.v !pw + 1 else 0)
  {
    let w = !pw;
    with s . assert (pts_to a s);
    seq_pre_perm pre s0 s;
    let res = merge_pass impl_cmp a tmp w #_ #s0;
    if res {
      with st . assert (pts_to tmp st);
      S.pts_to_len a;
      S.pts_to_len tmp;
      S.copy a tmp;
      perm_trans s0 s st;
      if (SZ.lte (SZ.sub n w) w) {
        runs_sorted_full cmp (2 * SZ.v w) st;
        pdone := true;
      } else {
        pw := SZ.add w w;
      }
    } else {
      pok := false;
    }
  };
  let ok = !pok;
  with s w done . assert (pts_to a s ** pts_to pw w ** pts_to pdone done);
  sort_inv_end cmp s0 s (SZ.v w) ok done;
  ok
}

#pop-options
