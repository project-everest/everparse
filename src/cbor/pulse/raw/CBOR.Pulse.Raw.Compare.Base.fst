module CBOR.Pulse.Raw.Compare.Base
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array.MergeSort
module SM = Pulse.Lib.SeqMatch
module GR = Pulse.Lib.GhostReference

let rec lex_compare
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Tot int
  (decreases l1)
= match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | a1 :: q1, [] -> 1
  | a1 :: q1, a2 :: q2 ->
    let c = compare a1 a2 in
    if c = 0
    then lex_compare compare q1 q2
    else c

let vmatch_slice_list
  (#tl #th: Type)
  (vmatch: tl -> th -> slprop)
  (p: perm)
  (sl: S.slice tl)
  (sh: list th)
: slprop
= exists* vl . pts_to sl #p vl **
  SM.seq_list_match vl sh vmatch

inline_for_extraction
```pulse
fn impl_lex_compare
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: A.impl_compare_t vmatch compare)
  (p: perm)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_slice_list vmatch p) (lex_compare compare)
= (s1: _)
  (s2: _)
  (#v1: _)
  (#v2: _)
{
  admit ()
}
```

module I16 = FStar.Int16

inline_for_extraction
let impl_compare_scalar_t
  (#th: Type)
  (compare: th -> th -> int)
= (x1: th) ->
  (x2: th) ->
  stt I16.t
    emp
    (fun res -> pure (
      let v = compare x1 x2 in
      (v < 0 <==> I16.v res < 0) /\
      (v > 0 <==> I16.v res > 0)
    ))

let eq_as_slprop (t: Type) (x x': t) : slprop = pure (x == x')

inline_for_extraction
```pulse
fn impl_compare_of_impl_compare_scalar
  (#th: Type0)
  (compare: Ghost.erased (th -> th -> int))
  (impl: impl_compare_scalar_t compare)
: A.impl_compare_t u#0 u#0 #_ #_ (eq_as_slprop th) (Ghost.reveal compare)
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  admit ()
}
```

let vmatch_slice_list_scalar
  (#th: Type)
  (p: perm)
  (sl: S.slice th)
  (sh: list th)
: slprop
= pts_to sl #p (Seq.seq_of_list sh)

module Trade = Pulse.Lib.Trade.Util

```pulse
ghost
fn vmatch_slice_list_of_vmatch_slice_list_scalar
  (#th: Type)
  (p: perm)
  (sl: S.slice th)
  (sh: list th)
requires
  vmatch_slice_list_scalar p sl sh
ensures
  vmatch_slice_list (eq_as_slprop th) p sl sh **
  Trade.trade
    (vmatch_slice_list (eq_as_slprop th) p sl sh)
    (vmatch_slice_list_scalar p sl sh)
{
  admit ()
}
```

inline_for_extraction
```pulse
fn impl_lex_compare_scalar
  (#th: Type0)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: impl_compare_scalar_t compare)
  (p: perm)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_slice_list_scalar p) (lex_compare compare)
= (s1: _)
  (s2: _)
  (#v1: _)
  (#v2: _)
{
  vmatch_slice_list_of_vmatch_slice_list_scalar p s1 v1;
  vmatch_slice_list_of_vmatch_slice_list_scalar p s2 v2;
  let res =
    impl_lex_compare _ _
      (impl_compare_of_impl_compare_scalar compare impl_compare)
      _ s1 s2;
  Trade.elim _ (vmatch_slice_list_scalar p s1 _);
  Trade.elim _ (vmatch_slice_list_scalar p s2 _);
  res
}
```
