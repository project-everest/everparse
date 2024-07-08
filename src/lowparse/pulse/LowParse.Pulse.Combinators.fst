module LowParse.Pulse.Combinators
include LowParse.Spec.Combinators
include LowParse.Pulse.Base
open FStar.Tactics.V2
open LowParse.Pulse.Util
open Pulse.Lib.Stick
open Pulse.Lib.Slice

module SZ = FStar.SizeT

let parse_serialize_strong_prefix
  (#t: Type)
  (#k: parser_kind)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (v: t)
  (suff: bytes)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    let sv = bare_serialize s v in
    parse p (sv `Seq.append` suff) == Some (v, Seq.length sv)
  ))
= let sv = bare_serialize s v in
  parse_strong_prefix #k p sv (sv `Seq.append` suff)

let split_nondep_then_post'
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased (t1 & t2))
  (left right: slice byte)
: Tot vprop
= pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v) **
  ((pts_to_serialized s1 left #pm (fst v) **
  pts_to_serialized s2 right #pm (snd v)) @==>
    pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)

let split_nondep_then_post
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (pm: perm)
  (v: Ghost.erased (t1 & t2))
  (res: (slice byte & slice byte))
: Tot vprop
= let (left, right) = res in
  split_nondep_then_post' s1 s2 input pm v left right

```pulse
fn split_nondep_then
  (#t1 #t2: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (j1: jumper p1)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (t1 & t2))
  requires pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v
  returns res: (slice byte & slice byte)
  ensures split_nondep_then_post s1 s2 input pm v res
{
  tot_serialize_nondep_then_eq s1 s2 v;
  rewrite (pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)
    as (pts_to input #pm (bare_serialize s1 (fst v) `Seq.append` bare_serialize s2 (snd v)));
  parse_serialize_strong_prefix s1 (fst v) (bare_serialize s2 (snd v));
  let i = j1 input 0sz;
  let res = slice_append_split false input i;
  match res {
    Mktuple2 input1 input2 -> {
      unfold (slice_append_split_post input pm (bare_serialize s1 (fst v)) (bare_serialize s2 (snd v)) i res);
      unfold (slice_append_split_post' input pm (bare_serialize s1 (fst v)) (bare_serialize s2 (snd v)) i input1 input2);
      fold (pts_to_serialized s1 input1 #pm (fst v));
      fold (pts_to_serialized s2 input2 #pm (snd v));
      ghost
      fn aux
        (_foo: unit)
        requires is_split input pm i input1 input2 ** (pts_to_serialized s1 input1 #pm (fst v) ** pts_to_serialized s2 input2 #pm (snd v))
        ensures pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v
      {
        unfold (pts_to_serialized s1 input1 #pm (fst v));
        unfold (pts_to_serialized s2 input2 #pm (snd v));
        join input1 input2 input;
        rewrite (pts_to input #pm (bare_serialize s1 (fst v) `Seq.append` bare_serialize s2 (snd v)))
          as (pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)
      };
      intro_stick
        (pts_to_serialized s1 input1 #pm (fst v) ** pts_to_serialized s2 input2 #pm (snd v))
        (pts_to_serialized (tot_serialize_nondep_then s1 s2) input #pm v)
        (is_split input pm i input1 input2)
        aux;
      fold (split_nondep_then_post' s1 s2 input pm v input1 input2);
      fold (split_nondep_then_post s1 s2 input pm v (input1, input2));
      (input1, input2)
    }
  }
}
```
