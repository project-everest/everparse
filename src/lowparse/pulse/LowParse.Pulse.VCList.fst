module LowParse.Pulse.VCList
include LowParse.Spec.VCList
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Stick
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference

inline_for_extraction
```pulse
fn jump_nlist
   (#t: Type0)
   (#k: parser_kind)
   (#p: parser k t)
   (j: jumper p)
   (n0: SZ.t)
: jumper #(nlist (SZ.v n0) t) #(parse_nlist_kind (SZ.v n0) k) (tot_parse_nlist (SZ.v n0) p)
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
    let pr0 = parse_consume (tot_parse_nlist (SZ.v n0) p) (Seq.slice v (SZ.v offset0) (Seq.length v)) in
    let pr = parse_consume (tot_parse_nlist (SZ.v n) p) (Seq.slice v (SZ.v offset) (Seq.length v)) in
    Some? pr0 /\ Some? pr /\
    SZ.v offset0 + Some?.v pr0 == SZ.v offset + Some?.v pr /\
    b == (SZ.v n > 0)
  ))) {
    let n = !pn;
    let offset = !poffset;
    tot_parse_nlist_eq (SZ.v n) p (Seq.slice v (SZ.v offset) (Seq.length v));
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
  pts_to_serialized (tot_serialize_nlist n s) input #pm v
ensures exists* v' .
  pts_to_serialized (tot_serialize_nondep_then s (tot_serialize_nlist (n - 1) s)) input #pm v' **
  (pts_to_serialized (tot_serialize_nondep_then s (tot_serialize_nlist (n - 1) s)) input #pm v' @==> pts_to_serialized (tot_serialize_nlist n s) input #pm v) **
  pure (
    v == (fst v' :: snd v')
  )
{
  synth_inverse_1 t (n - 1);
  synth_inverse_2 t (n - 1);
  rewrite_with_stick
    (pts_to_serialized (tot_serialize_nlist n s) input #pm v)
    (pts_to_serialized (tot_serialize_synth _ (synth_nlist (n - 1)) (tot_serialize_nondep_then s (tot_serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()) input #pm v);
  pts_to_serialized_synth_l2r_stick
    (tot_serialize_nondep_then s (tot_serialize_nlist' (n - 1) s))
    (synth_nlist (n - 1))
    (synth_nlist_recip (n - 1))
    input;
  stick_trans (pts_to_serialized (tot_serialize_nondep_then s (tot_serialize_nlist (n - 1) s)) input #pm _) _ _
}
```

inline_for_extraction
```pulse
fn nlist_hd
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (n: pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (tot_serialize_nlist n s) input #pm v
returns input' : slice byte
ensures exists* v' .
  pts_to_serialized s input' #pm v' **
  (pts_to_serialized s input' #pm v' @==> pts_to_serialized (tot_serialize_nlist n s) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.hd v
  )
{
  nlist_cons_as_nondep_then s n input;
  let res = nondep_then_fst s j (tot_serialize_nlist (n - 1) s) input;
  stick_trans (pts_to_serialized s res #pm _) _ _;
  res
}
```

inline_for_extraction
```pulse
fn nlist_tl
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (n: pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (tot_serialize_nlist n s) input #pm v
returns input' : slice byte
ensures exists* v' .
  pts_to_serialized (tot_serialize_nlist (n - 1) s) input' #pm v' **
  (pts_to_serialized (tot_serialize_nlist (n - 1) s) input' #pm v' @==> pts_to_serialized (tot_serialize_nlist n s) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.tl v
  )
{
  nlist_cons_as_nondep_then s n input;
  let res = nondep_then_snd s j (tot_serialize_nlist (n - 1) s) input;
  stick_trans (pts_to_serialized (tot_serialize_nlist (n - 1) s) res #pm _) _ _;
  res
}
```

inline_for_extraction
```pulse
fn nlist_nth
   (#t: Type0)
   (#k: parser_kind)
   (#p: parser k t)
   (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
   (j: jumper p)
   (n0: SZ.t)
  (input: slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist (SZ.v n0) t))
  (i0: SZ.t { SZ.v i0 < SZ.v n0 })
requires
  pts_to_serialized (tot_serialize_nlist (SZ.v n0) s) input #pm v0
returns input' : slice byte
ensures exists* v .
  pts_to_serialized s input' #pm v **
  (pts_to_serialized s input' #pm v @==> pts_to_serialized (tot_serialize_nlist (SZ.v n0) s) input #pm v0) **
  pure (v == List.Tot.index v0 (SZ.v i0))
{
  stick_id (pts_to_serialized (tot_serialize_nlist (SZ.v n0) s) input #pm v0);
  let mut pi = 0sz;
  let mut pres = input;
  while (
    let i = !pi;
    (SZ.lt i i0)
  ) invariant b . exists* i res (n: nat) (v: nlist n t) . (
    R.pts_to pi i ** R.pts_to pres res **
    pts_to_serialized (tot_serialize_nlist n s) res #pm v **
    (pts_to_serialized (tot_serialize_nlist n s) res #pm v @==> pts_to_serialized (tot_serialize_nlist (SZ.v n0) s) input #pm v0) **
    pure (
      SZ.v i <= SZ.v i0 /\
      (b == (SZ.v i < SZ.v i0)) /\
      n == SZ.v n0 - SZ.v i /\
      List.Tot.index v0 (SZ.v i0) == List.Tot.index v (SZ.v i0 - SZ.v i)
  )) {
    let res = !pres;
    let i = !pi;
    let res2 = nlist_tl s j (SZ.v n0 - SZ.v i) res;
    pi := (SZ.add i 1sz);
    pres := res2;
    stick_trans
      (pts_to_serialized (tot_serialize_nlist (SZ.v n0 - SZ.v i - 1) s) res2 #pm _)
      _
      _
  };
  let res = !pres;
  let res2 = nlist_hd s j (SZ.v n0 - SZ.v i0) res;
  stick_trans
    (pts_to_serialized s res2 #pm _) _ _;
  res2
}
```
