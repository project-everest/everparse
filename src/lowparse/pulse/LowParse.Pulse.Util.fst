module LowParse.Pulse.Util
include Pulse.Lib.Pervasives
include Pulse.Lib.Stick

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

```pulse
ghost
fn stick_trans
  (p1 p2 p3: vprop)
  requires (p1 @==> p2) ** (p2 @==> p3)
  ensures (p1 @==> p3)
{
  ghost
  fn aux
    (_foo: unit)
  requires ((p1 @==> p2) ** (p2 @==> p3)) ** p1
  ensures p3
  {
    elim_stick p1 p2;
    elim_stick p2 p3
  };
  intro_stick p1 p3 ((p1 @==> p2) ** (p2 @==> p3)) aux
}
```

```pulse
ghost
fn stick_reg_l
  (p p1 p2: vprop)
  requires (p1 @==> p2)
  ensures ((p ** p1) @==> (p ** p2))
{
  ghost
  fn aux
    (_foo: unit)
  requires ((p1 @==> p2) ** (p ** p1))
  ensures (p ** p2)
  {
    elim_stick p1 p2
  };
  intro_stick (p ** p1) (p ** p2) (p1 @==> p2) aux
}
```

```pulse
ghost
fn stick_eq
  (p1 p2: vprop)
  requires pure (p1 == p2) // ideally with `vprop_equivs ()`
  ensures (p1 @==> p2)
{
  ghost
  fn aux
    (_foo: unit)
  requires pure (p1 == p2) ** p1
  ensures p2
  {
    rewrite p1 as p2
  };
  intro_stick p1 p2 (pure (p1 == p2)) aux
}
```

```pulse
ghost
fn stick_rewrite_l
  (l1 l2 r: vprop)
  requires (l1 @==> r) ** pure (l1 == l2)
  ensures l2 @==> r
{
  rewrite (l1 @==> r) as (l2 @==> r)
}
```

```pulse
ghost
fn stick_rewrite_r
  (l r1 r2: vprop)
  requires (l @==> r1) ** pure (r1 == r2)
  ensures l @==> r2
{
  rewrite (l @==> r1) as (l @==> r2)
}
```

```pulse
ghost
fn stick_reg_r
  (p1 p2 p: vprop)
  requires (p1 @==> p2)
  ensures ((p1 ** p) @==> (p2 ** p))
{
  stick_reg_l p p1 p2;
  vprop_equivs ();
  rewrite ((p ** p1) @==> (p ** p2))
    as ((p1 ** p) @==> (p2 ** p))
}
```

```pulse
ghost
fn stick_weak_concl_l
  (p1 p2 p: vprop)
  requires (p1 @==> p2) ** p
  ensures (p1 @==> (p ** p2))
{
  ghost
  fn aux
    (_foo: unit)
    requires ((p1 @==> p2) ** p) ** p1
    ensures p ** p2
  {
    elim_stick p1 p2
  };
  intro_stick p1 (p ** p2) ((p1 @==> p2) ** p) aux
}
```

```pulse
ghost
fn stick_weak_concl_r
  (p1 p2 p: vprop)
  requires (p1 @==> p2) ** p
  ensures (p1 @==> (p2 ** p))
{
  stick_weak_concl_l p1 p2 p;
  vprop_equivs ();
  stick_eq (p ** p2) (p2 ** p);
  stick_trans p1 _ _
}
```

```pulse
ghost
fn stick_prod
  (l1 r1 l2 r2: vprop)
  requires ((l1 @==> r1) ** (l2 @==> r2))
  ensures ((l1 ** l2) @==> (r1 ** r2))
{
  ghost
  fn aux
    (_foo: unit)
    requires ((l1 @==> r1) ** (l2 @==> r2)) ** (l1 ** l2)
    ensures r1 ** r2
  {
    elim_stick l1 r1;
    elim_stick l2 r2
  };
  intro_stick (l1 ** l2) (r1 ** r2) ((l1 @==> r1) ** (l2 @==> r2)) aux
}
```

```pulse
ghost
fn stick_elim_partial_l
  (p p1 p2: vprop)
  requires p ** ((p ** p1) @==> p2)
  ensures p1 @==> p2
{
  ghost
  fn aux
    (_foo: unit)
  requires (p ** ((p ** p1) @==> p2)) ** p1
  ensures p2
  {
    elim_stick (p ** p1) p2
  };
  intro_stick p1 p2 (p ** ((p ** p1) @==> p2)) aux
}
```

```pulse
ghost
fn stick_elim_partial_r
  (p1 p p2: vprop)
  requires ((p1 ** p) @==> p2) ** p
  ensures p1 @==> p2
{
  vprop_equivs ();
  stick_rewrite_l (p1 ** p) (p ** p1) p2;
  stick_elim_partial_l p p1 p2
}
```

noeq type slice_pair (t: Type) = | SlicePair: (fst: S.slice t) -> (snd: S.slice t) -> slice_pair t

let split_post0
    (#t: Type) (s: S.slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: (slice_pair t))
: Tot vprop
= let SlicePair s1 s2 = res in
    S.split_post' s p v i s1 s2

```pulse
fn slice_split (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p v ** pure (S.split_precond mutb p v i)
    returns res: slice_pair t
    ensures split_post0 s p v i res
{
  admit ()
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
    (res: slice_pair t)
: Tot vprop
= let SlicePair s1 s2 = res in
  slice_append_split_post' s p v1 v2 i s1 s2

inline_for_extraction
noextract
```pulse
fn slice_append_split (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v1 #v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p (v1 `Seq.append` v2) ** pure (slice_append_split_precond mutb p v1 i)
    returns res: slice_pair t
    ensures slice_append_split_post  s p v1 v2 i res
{
  let vs = Ghost.hide (Seq.split (Seq.append v1 v2) (SZ.v i));
  assert (pure (fst vs `Seq.equal` v1));
  assert (pure (snd vs `Seq.equal` v2));
  let res = slice_split mutb s i;
  match res {
    SlicePair s1 s2 -> {
      unfold (split_post0 s p (Seq.append v1 v2) i res);
      unfold (S.split_post' s p (Seq.append v1 v2) i s1 s2);
      fold (slice_append_split_post' s p v1 v2 i s1 s2);
      fold (slice_append_split_post s p v1 v2 i (SlicePair s1 s2));
      (SlicePair s1 s2)
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
            ((S.pts_to s1 #p v1 ** S.pts_to s2 #p v2) @==> S.pts_to s #p (v1 `Seq.append` v2))

let slice_append_split_stick_post
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: slice_pair t)
: Tot vprop
= let SlicePair s1 s2 = res in
  slice_append_split_stick_post' s p v1 v2 i s1 s2

inline_for_extraction
noextract
```pulse
fn slice_append_split_stick (#t: Type) (mutb: bool) (input: S.slice t) (#p: perm) (#v1 #v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to input #p (v1 `Seq.append` v2) ** pure (slice_append_split_precond mutb p v1 i)
    returns res: slice_pair t
    ensures slice_append_split_stick_post input p v1 v2 i res
{
  let res = slice_append_split mutb input i;
  match res {
    SlicePair input1 input2 -> {
      unfold (slice_append_split_post input p v1 v2 i res);
      unfold (slice_append_split_post' input p v1 v2 i input1 input2);
      ghost
      fn aux
        (_foo: unit)
        requires S.is_split input p i input1 input2 ** (S.pts_to input1 #p v1 ** S.pts_to input2 #p v2)
        ensures S.pts_to input #p (v1 `Seq.append` v2)
      {
        S.join input1 input2 input;
      };
      intro_stick _ _ _ aux;
      fold (slice_append_split_stick_post' input p v1 v2 i input1 input2);
      fold (slice_append_split_stick_post input p v1 v2 i (SlicePair input1 input2));
      (SlicePair input1 input2)
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
            ((S.pts_to s1 #p v1 ** S.pts_to s2 #p v2) @==> S.pts_to s #p v) **
            pure (
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)
            )

let slice_split_stick_post
    (#t: Type) (s: S.slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: slice_pair t)
: Tot vprop
= let (SlicePair s1 s2) = res in
  slice_split_stick_post' s p v i s1 s2

inline_for_extraction
noextract
```pulse
fn slice_split_stick (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p v ** pure (S.split_precond mutb p v i)
    returns res: slice_pair t
    ensures slice_split_stick_post s p v i res
{
  Seq.lemma_split v (SZ.v i);
  let res = slice_split mutb s i;
  match res { SlicePair s1 s2 -> {
    unfold (split_post0 s p v i res);
    unfold (S.split_post' s p v i s1 s2);
    with v1 v2 . assert (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2);
    ghost
    fn aux
      (_: unit)
    requires (S.is_split s p i s1 s2 ** (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2))
    ensures (S.pts_to s #p v)
    {
      S.join s1 s2 s
    };
    intro_stick _ _ _ aux;
    fold (slice_split_stick_post' s p v i s1 s2);
    fold (slice_split_stick_post s p v i (SlicePair s1 s2));
    (SlicePair s1 s2)
  }}
}
```

```pulse
ghost
fn rewrite_with_stick
  (p1 p2: vprop)
  requires p1 ** pure (p1 == p2)
  ensures p2 ** (p2 @==> p1)
{
  rewrite p1 as p2;
  ghost
  fn aux
    (_: unit)
    requires emp ** p2
    ensures p1
  {
    rewrite p2 as p1
  };
  intro_stick _ _ _ aux
}
```
