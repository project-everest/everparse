module LowParse.Pulse.VCList
include LowParse.Spec.VCList
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
```pulse
fn jump_nlist
   (#t: Type0)
   (#k: Ghost.erased parser_kind)
   (#p: parser k t)
   (j: jumper p)
   (n0: SZ.t)
: jumper #(nlist (SZ.v n0) t) #(parse_nlist_kind (SZ.v n0) k) (parse_nlist (SZ.v n0) p)
=
  (input: slice byte)
  (offset0: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let mut pn = n0;
  let mut poffset = offset0;
  while (
    let n = !pn;
    (SZ.gt n 0sz)
  ) invariant b . exists* n offset . (
    pts_to input #pm v ** R.pts_to pn n ** R.pts_to poffset offset ** pure (
    SZ.v offset <= Seq.length v /\ (
    let pr0 = parse_consume (parse_nlist (SZ.v n0) p) (Seq.slice v (SZ.v offset0) (Seq.length v)) in
    let pr = parse_consume (parse_nlist (SZ.v n) p) (Seq.slice v (SZ.v offset) (Seq.length v)) in
    Some? pr0 /\ Some? pr /\
    SZ.v offset0 + Some?.v pr0 == SZ.v offset + Some?.v pr /\
    b == (SZ.v n > 0)
  ))) {
    let n = !pn;
    let offset = !poffset;
    parse_nlist_eq (SZ.v n) p (Seq.slice v (SZ.v offset) (Seq.length v));
    let offset' = j input offset;
    pn := (SZ.sub n 1sz);
    poffset := offset';
  };
  !poffset
}
```

```pulse
ghost
fn nlist_cons_as_nondep_then
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n: pos)
  (input: slice byte)
  (#pm: perm)
  (#v: nlist n t)
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
ensures exists* v' .
  pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm v' **
  trade (pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm v') (pts_to_serialized (serialize_nlist n s) input #pm v) **
  pure (
    v == (fst v' :: snd v')
  )
{
  synth_inverse_1 t (n - 1);
  synth_inverse_2 t (n - 1);
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_nlist n s) input #pm v)
    (pts_to_serialized (serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then s (serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()) input #pm v);
  pts_to_serialized_synth_l2r_trade
    (serialize_nondep_then s (serialize_nlist' (n - 1) s))
    (synth_nlist (n - 1))
    (synth_nlist_recip (n - 1))
    input;
  Trade.trans (pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm _) _ _
}
```

inline_for_extraction
```pulse
fn nlist_hd
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
returns input' : slice byte
ensures exists* v' .
  pts_to_serialized s input' #pm v' **
  trade (pts_to_serialized s input' #pm v') (pts_to_serialized (serialize_nlist n s) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.hd v
  )
{
  nlist_cons_as_nondep_then s n input;
  let res = nondep_then_fst #_ #(nlist (n - 1) t) s j #(parse_nlist_kind (n - 1) k) #(coerce_eq () (parse_nlist (n - 1) p)) (coerce_eq () (serialize_nlist (n - 1) s <: serializer #(parse_nlist_kind (n - 1) k) (parse_nlist (n - 1) p))) input; // FIXME: WHY WHY WHY are those reveal (hide (...)) NOT reduced?
  Trade.trans (pts_to_serialized s res #pm _) _ _;
  res
}
```

inline_for_extraction
```pulse
fn nlist_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
returns input' : slice byte
ensures exists* v' .
  pts_to_serialized (serialize_nlist (n - 1) s) input' #pm v' **
  trade (pts_to_serialized (serialize_nlist (n - 1) s) input' #pm v') (pts_to_serialized (serialize_nlist n s) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.tl v
  )
{
  nlist_cons_as_nondep_then s n input;
  let res = nondep_then_snd #_ #(nlist (n - 1) t) s j #(parse_nlist_kind (n - 1) k) #(coerce_eq () (parse_nlist (n - 1) p)) (coerce_eq () (serialize_nlist (n - 1) s <: serializer (parse_nlist (n - 1) p))) input; // FIXME: same as above
  Trade.trans (pts_to_serialized (serialize_nlist (n - 1) s) res #pm _) _ _;
  res
}
```

inline_for_extraction
```pulse
fn nlist_nth
   (#t: Type0)
   (#k: Ghost.erased parser_kind)
   (#p: parser k t)
   (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
   (j: jumper p)
   (n0: Ghost.erased nat)
  (input: slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist n0 t))
  (i0: SZ.t { SZ.v i0 < n0 })
requires
  pts_to_serialized (serialize_nlist n0 s) input #pm v0
returns input' : slice byte
ensures exists* v .
  pts_to_serialized s input' #pm v **
  trade (pts_to_serialized s input' #pm v) (pts_to_serialized (serialize_nlist n0 s) input #pm v0) **
  pure (v == List.Tot.index v0 (SZ.v i0))
{
  Trade.refl (pts_to_serialized (serialize_nlist n0 s) input #pm v0);
  let mut pi = 0sz;
  let mut pres = input;
  while (
    let i = !pi;
    (SZ.lt i i0)
  ) invariant b . exists* i res (n: nat) (v: nlist n t) . (
    R.pts_to pi i ** R.pts_to pres res **
    pts_to_serialized (serialize_nlist n s) res #pm v **
    trade (pts_to_serialized (serialize_nlist n s) res #pm v) (pts_to_serialized (serialize_nlist n0 s) input #pm v0) **
    pure (
      SZ.v i <= SZ.v i0 /\
      (b == (SZ.v i < SZ.v i0)) /\
      n == n0 - SZ.v i /\
      List.Tot.index v0 (SZ.v i0) == List.Tot.index v (SZ.v i0 - SZ.v i)
  )) {
    let res = !pres;
    let i = !pi;
    let res2 = nlist_tl s j (n0 - SZ.v i) res;
    pi := (SZ.add i 1sz);
    pres := res2;
    Trade.trans
      (pts_to_serialized (serialize_nlist (n0 - SZ.v i - 1) s) res2 #pm _)
      _
      _
  };
  let res = !pres;
  let res2 = nlist_hd s j (n0 - SZ.v i0) res;
  Trade.trans
    (pts_to_serialized s res2 #pm _) _ _;
  res2
}
```

let synth_nlist_1
  (#t: Type)
  (x: t)
: Tot (nlist 1 t)
= [x]

let synth_nlist_1_recip
  (#t: Type)
  (x: nlist 1 t)
: Tot t
= List.Tot.hd x

let parse_nlist_1_eq
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (b: bytes)
: Lemma
  (parse (parse_nlist 1 p) b == parse (parse_synth p synth_nlist_1) b)
= parse_nlist_eq 1 p b;
  parse_synth_eq p synth_nlist_1 b

```pulse
ghost
fn pts_to_serialized_nlist_1
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s input #pm v
  ensures exists* v' . pts_to_serialized (serialize_nlist 1 s) input #pm v' **
    trade (pts_to_serialized (serialize_nlist 1 s) input #pm v')
      (pts_to_serialized s input #pm v) **
    pure ((v' <: list t) == [v])
{
  pts_to_serialized_synth_trade s synth_nlist_1 synth_nlist_1_recip input;
  Classical.forall_intro (parse_nlist_1_eq p);
  pts_to_serialized_ext_trade
    (serialize_synth p synth_nlist_1 s synth_nlist_1_recip ())
    (serialize_nlist 1 s)
    input;
  Trade.trans
    (pts_to_serialized (serialize_nlist 1 s) input #pm _)
    _ _
}
```
