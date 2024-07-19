module LowParse.Pulse.Util
include Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = FStar.Tactics

```pulse
ghost
fn trade_id
  (#[T.exact (`emp_inames)] is:inames)
  (p: vprop)
requires emp
ensures (trade #is p p)
{
  ghost fn aux (_: unit)
    requires emp ** p
    ensures p
    opens is
  {
    ()
  };
  intro_trade p p emp aux
}
```

```pulse
ghost
fn trade_reg_l
  (#is : inames)
  (p p1 p2: vprop)
  requires (trade #is p1 p2)
  ensures (trade #is (p ** p1) (p ** p2))
{
  ghost
  fn aux
    (_foo: unit)
  requires ((trade #is p1 p2) ** (p ** p1))
  ensures (p ** p2)
  opens is
  {
    elim_trade #is p1 p2
  };
  intro_trade (p ** p1) (p ** p2) (trade #is p1 p2) aux
}
```

```pulse
ghost
fn trade_eq
  (#[T.exact (`emp_inames)] is:inames)
  (p1 p2: vprop)
  requires pure (p1 == p2) // ideally with `vprop_equivs ()`
  ensures (trade #is p1 p2)
{
  ghost
  fn aux
    (_foo: unit)
  requires pure (p1 == p2) ** p1
  ensures p2
  opens is
  {
    rewrite p1 as p2
  };
  intro_trade p1 p2 (pure (p1 == p2)) aux
}
```

```pulse
ghost
fn trade_reg_r
  (#is: inames)
  (p1 p2 p: vprop)
  requires (trade #is p1 p2)
  ensures (trade #is (p1 ** p) (p2 ** p))
{
  trade_reg_l p p1 p2;
  vprop_equivs ();
  rewrite (trade #is (p ** p1) (p ** p2))
    as (trade #is (p1 ** p) (p2 ** p))
}
```

```pulse
ghost
fn trade_weak_concl_l
  (#is: inames)
  (p1 p2 p: vprop)
  requires (trade #is p1 p2) ** p
  ensures (trade #is p1 (p ** p2))
{
  ghost
  fn aux
    (_foo: unit)
    requires ((trade #is p1 p2) ** p) ** p1
    ensures p ** p2
    opens is
  {
    elim_trade #is p1 p2
  };
  intro_trade p1 (p ** p2) ((trade #is p1 p2) ** p) aux
}
```

```pulse
ghost
fn trade_weak_concl_r
  (#is: inames)
  (p1 p2 p: vprop)
  requires (trade #is p1 p2) ** p
  ensures (trade #is p1 (p2 ** p))
{
  trade_weak_concl_l p1 p2 p;
  vprop_equivs ();
  trade_eq is (p ** p2) (p2 ** p); // FIXME: why is the `is`  argument explicit?
  trade_compose p1 _ _
}
```

```pulse
ghost
fn trade_prod
  (#is: inames)
  (l1 r1 l2 r2: vprop)
  requires (trade #is l1 r1 ** trade #is l2 r2)
  ensures (trade #is (l1 ** l2) (r1 ** r2))
{
  ghost
  fn aux
    (_foo: unit)
    requires ((trade #is l1 r1) ** (trade #is l2 r2)) ** (l1 ** l2)
    ensures r1 ** r2
    opens is
  {
    elim_trade #is l1 r1;
    elim_trade #is l2 r2
  };
  intro_trade (l1 ** l2) (r1 ** r2) ((trade #is l1 r1) ** (trade #is l2 r2)) aux
}
```

```pulse
ghost
fn trade_elim_partial_l
  (#is: inames)
  (p p1 p2: vprop)
  requires p ** (trade #is (p ** p1) p2)
  ensures trade #is p1 p2
{
  ghost
  fn aux
    (_foo: unit)
  requires (p ** (trade #is (p ** p1) p2)) ** p1
  ensures p2
  opens is
  {
    elim_trade #is (p ** p1) p2
  };
  intro_trade p1 p2 (p ** (trade #is (p ** p1) p2)) aux
}
```

```pulse
ghost
fn trade_elim_partial_r
  (#is: inames)
  (p1 p p2: vprop)
  requires (trade #is (p1 ** p) p2) ** p
  ensures trade #is p1 p2
{
  vprop_equivs ();
  rewrite (trade #is (p1 ** p) p2)
    as (trade #is (p ** p1) p2);
  trade_elim_partial_l p p1 p2
}
```

noextract
let slice_append_split_precond
  (#t: Type) (mutb: bool) (p: perm) (v1: Ghost.erased (Seq.seq t)) (i: SZ.t)
: Tot prop
= SZ.v i == Seq.length v1 /\ (mutb == true ==> p == 1.0R)

let slice_append_split_post'
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: S.slice t)
    (s2: S.slice t)
: Tot vprop
=
            S.pts_to s1 #p v1 **
            S.pts_to s2 #p v2 **
            S.is_split s p i s1 s2

let slice_append_split_post
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: S.slice_pair t)
: Tot vprop
= let S.SlicePair s1 s2 = res in
  slice_append_split_post' s p v1 v2 i s1 s2

inline_for_extraction
noextract
```pulse
fn slice_append_split (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v1 #v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p (v1 `Seq.append` v2) ** pure (slice_append_split_precond mutb p v1 i)
    returns res: S.slice_pair t
    ensures slice_append_split_post  s p v1 v2 i res
{
  let vs = Ghost.hide (Seq.split (Seq.append v1 v2) (SZ.v i));
  assert (pure (fst vs `Seq.equal` v1));
  assert (pure (snd vs `Seq.equal` v2));
  let res = S.split mutb s i;
  match res {
    S.SlicePair s1 s2 -> {
      unfold (S.split_post s p (Seq.append v1 v2) i res);
      unfold (S.split_post' s p (Seq.append v1 v2) i s1 s2);
      fold (slice_append_split_post' s p v1 v2 i s1 s2);
      fold (slice_append_split_post s p v1 v2 i (S.SlicePair s1 s2));
      (S.SlicePair s1 s2)
    }
  }
}
```

let slice_append_split_stick_post'
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: S.slice t)
    (s2: S.slice t)
: Tot vprop
=
            S.pts_to s1 #p v1 **
            S.pts_to s2 #p v2 **
            (trade (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2) (S.pts_to s #p (v1 `Seq.append` v2)))

let slice_append_split_stick_post
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: S.slice_pair t)
: Tot vprop
= let S.SlicePair s1 s2 = res in
  slice_append_split_stick_post' s p v1 v2 i s1 s2

```pulse
ghost
fn slice_append_split_stick_aux
  (#t: Type) (input: S.slice t) (p: perm) (v1 v2: (Seq.seq t)) (i: SZ.t) (input1 input2: S.slice t) (_: unit)
    requires S.is_split input p i input1 input2 ** (S.pts_to input1 #p v1 ** S.pts_to input2 #p v2)
    ensures S.pts_to input #p (v1 `Seq.append` v2)
{
  S.join input1 input2 input
}
```

inline_for_extraction
noextract
```pulse
fn slice_append_split_stick (#t: Type) (mutb: bool) (input: S.slice t) (#p: perm) (#v1 #v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to input #p (v1 `Seq.append` v2) ** pure (slice_append_split_precond mutb p v1 i)
    returns res: S.slice_pair t
    ensures slice_append_split_stick_post input p v1 v2 i res
{
  let res = slice_append_split mutb input i;
  match res {
    S.SlicePair input1 input2 -> {
      unfold (slice_append_split_post input p v1 v2 i res);
      unfold (slice_append_split_post' input p v1 v2 i input1 input2);
      intro_trade _ _ _ (slice_append_split_stick_aux input p v1 v2 i input1 input2);
      fold (slice_append_split_stick_post' input p v1 v2 i input1 input2);
      fold (slice_append_split_stick_post input p v1 v2 i (S.SlicePair input1 input2));
      (S.SlicePair input1 input2)
    }
  }
}
```

let slice_split_stick_post'
    (#t: Type) (s: S.slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: S.slice t)
    (s2: S.slice t)
: Tot vprop
= exists* v1 v2 .
            S.pts_to s1 #p v1 **
            S.pts_to s2 #p v2 **
            (trade (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2) (S.pts_to s #p v)) **
            pure (
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)
            )

let slice_split_stick_post
    (#t: Type) (s: S.slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: S.slice_pair t)
: Tot vprop
= let (S.SlicePair s1 s2) = res in
  slice_split_stick_post' s p v i s1 s2

```pulse
ghost
fn slice_split_stick_aux
  (#t: Type) (s: S.slice t) (p: perm) (v: Seq.seq t) (i: SZ.t)
  (s1 s2: S.slice t) (v1 v2: Seq.seq t) (hyp: squash (v == Seq.append v1 v2)) (_: unit)
    requires (S.is_split s p i s1 s2 ** (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2))
    ensures (S.pts_to s #p v)
    {
      S.join s1 s2 s
    }
```

inline_for_extraction
noextract
```pulse
fn slice_split_stick (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p v ** pure (S.split_precond mutb p v i)
    returns res: S.slice_pair t
    ensures slice_split_stick_post s p v i res
{
  Seq.lemma_split v (SZ.v i);
  let res = S.split mutb s i;
  match res { S.SlicePair s1 s2 -> {
    unfold (S.split_post s p v i res);
    unfold (S.split_post' s p v i s1 s2);
    with v1 v2 . assert (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2);
    intro_trade _ _ _ (slice_split_stick_aux s p v i s1 s2 v1 v2 ());
    fold (slice_split_stick_post' s p v i s1 s2);
    fold (slice_split_stick_post s p v i (S.SlicePair s1 s2));
    (S.SlicePair s1 s2)
  }}
}
```

```pulse
ghost
fn rewrite_with_trade
  (#[T.exact (`emp_inames)] is:inames)
  (p1 p2: vprop)
  requires p1 ** pure (p1 == p2)
  ensures p2 ** (trade #is p2 p1)
{
  rewrite p1 as p2;
  ghost
  fn aux
    (_: unit)
    requires emp ** p2
    ensures p1
    opens is
  {
    rewrite p2 as p1
  };
  intro_trade _ _ _ aux
}
```
