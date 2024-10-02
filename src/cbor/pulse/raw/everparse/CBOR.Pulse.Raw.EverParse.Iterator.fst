module CBOR.Pulse.Raw.EverParse.Iterator
open CBOR.Pulse.Raw.Util
open CBOR.Pulse.Raw.Iterator
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module LP = LowParse.Pulse.VCList

noeq
type cbor_raw_serialized_iterator = {
  s: S.slice LP.byte;
  len: Ghost.erased nat;
}

let cbor_raw_serialized_iterator_match
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
: Tot slprop
= exists* l' . LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l' ** pure (l == l')

```pulse
ghost
fn cbor_raw_serialized_iterator_unfold
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
requires
  cbor_raw_serialized_iterator_match s pm c l
returns res: squash (List.Tot.length l == c.len)
ensures
  LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l **
  trade
    (LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l)
    (cbor_raw_serialized_iterator_match s pm c l)
{
  unfold (cbor_raw_serialized_iterator_match s pm c l);
  ghost fn aux (_: unit)
    requires (emp ** LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l)
    ensures (cbor_raw_serialized_iterator_match s pm c l)
  {
    fold (cbor_raw_serialized_iterator_match s pm c l)
  };
  Trade.intro _ _ _ aux;
  ()
}
```

```pulse
ghost
fn cbor_raw_serialized_iterator_fold
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: LP.nlist (c.len) elt_high)
requires
  LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l
ensures
  cbor_raw_serialized_iterator_match s pm c l **
  trade
    (cbor_raw_serialized_iterator_match s pm c l)
    (LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l)
{
  fold (cbor_raw_serialized_iterator_match s pm c l);
  ghost fn aux (_: unit)
    requires (emp ** cbor_raw_serialized_iterator_match s pm c l)
    ensures (LP.pts_to_serialized (LP.serialize_nlist (c.len) s) c.s #pm l)
  {
    unfold (cbor_raw_serialized_iterator_match s pm c l)
  };
  Trade.intro _ _ _ aux;
  ()
}
```

```pulse
ghost
fn cbor_raw_serialized_iterator_is_empty_equiv
  (#elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong /\ k.parser_kind_low > 0 })
  (pm: perm)
  (c: cbor_raw_serialized_iterator)
  (l: list elt_high)
requires
  cbor_raw_serialized_iterator_match s pm c l
ensures
  cbor_raw_serialized_iterator_match s pm c l ** pure (Nil? l <==> S.len c.s == 0sz)
{
  cbor_raw_serialized_iterator_unfold s pm c l;
  LP.pts_to_serialized_elim_trade (LP.serialize_nlist (c.len) s) c.s;
  S.pts_to_len c.s;
  Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm c l);
  Trade.elim _ _;
  let b : bool = Ghost.reveal c.len = 0;
  if (b) {
    ()
  } else {
    LP.serialize_nlist_cons (c.len - 1) s (List.Tot.hd l) (List.Tot.tl l);
    ()
  }
}
```

inline_for_extraction
```pulse
fn cbor_raw_serialized_iterator_is_empty
  (#elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong /\ (Ghost.reveal k).parser_kind_low > 0 })
: cbor_raw_serialized_iterator_is_empty_t #elt_high #cbor_raw_serialized_iterator (cbor_raw_serialized_iterator_match s)
= (c: cbor_raw_serialized_iterator)
  (#pm: perm)
  (#l: Ghost.erased (list elt_high))
{
  cbor_raw_serialized_iterator_is_empty_equiv s pm c l;
  (S.len c.s = 0sz)
}
```

let cbor_raw_serialized_iterator_next_cont
  (#elt_low #elt_high: Type0)
  (#k: LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { k.parser_kind_subkind == Some LP.ParserStrong })
  (elt_match: perm -> elt_low -> elt_high -> slprop)
= (x: S.slice LP.byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased elt_high) ->
  stt elt_low
    (LP.pts_to_serialized s x #pm v)
    (fun res -> exists* pm' . elt_match pm' res v **
      trade
        (elt_match pm' res v)
        (LP.pts_to_serialized s x #pm v)
    )

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
```pulse
fn cbor_raw_serialized_iterator_next
  (#elt_low #elt_high: Type0)
  (#k: Ghost.erased LP.parser_kind)
  (#p: LP.parser k elt_high)
  (s: LP.serializer p { (Ghost.reveal k).parser_kind_subkind == Some LP.ParserStrong /\ (Ghost.reveal k).parser_kind_low > 0 })
  (j: LP.jumper p)
  (elt_match: perm -> elt_low -> elt_high -> slprop)
  (phi: cbor_raw_serialized_iterator_next_cont s elt_match)
: cbor_raw_serialized_iterator_next_t #elt_low #elt_high #cbor_raw_serialized_iterator elt_match (cbor_raw_serialized_iterator_match s)
=
  (pi: R.ref (cbor_raw_iterator elt_low cbor_raw_serialized_iterator))
  (#pm: perm)
  (i: cbor_raw_serialized_iterator)
  (#l: Ghost.erased (list elt_high))
{
  cbor_raw_serialized_iterator_unfold s pm i l;
  LP.nlist_cons_as_nondep_then s i.len i.s;
  Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm i l);
  let len' : Ghost.erased nat = i.len - 1;
  let k' : Ghost.erased LP.parser_kind = LP.parse_nlist_kind len' k;
  let p' : LP.parser k' (LP.nlist len' elt_high) = LP.parse_nlist len' p;
  let s' : LP.serializer p' = LP.serialize_nlist len' s;
  let v' : Ghost.erased (elt_high & LP.nlist len' elt_high) = (List.Tot.hd l, List.Tot.tl l);
  assert (LP.pts_to_serialized
    (LPC.serialize_nondep_then s s')
    i.s
    #pm
    v'
  );
  let sp = LowParse.Pulse.Combinators.split_nondep_then
    s
    j
    #k'
    #p'
    s'
    i.s;
  match sp {
    SlicePair s1 s2 -> {
      unfold (LPC.split_nondep_then_post s s' i.s pm v' sp);
      unfold (LPC.split_nondep_then_post' s s' i.s pm v' s1 s2);
      Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm i l);
      let res = phi s1;
      with pm' . assert (elt_match pm' res (fst v'));
      Trade.rewrite_with_trade
        (elt_match pm' res (fst v'))
        (elt_match pm' res (List.Tot.hd l));
      Trade.trans (elt_match pm' res (List.Tot.hd l)) _ _;
      let i' : cbor_raw_serialized_iterator = {
        s = s2;
        len = len';
      };
      pi := CBOR_Raw_Iterator_Serialized i';
      cbor_raw_serialized_iterator_fold s pm i' (List.Tot.tl l);
      Trade.prod
        (elt_match _ res (List.Tot.hd l))
        _
        (cbor_raw_serialized_iterator_match s pm i' (List.Tot.tl l))
        _;
      Trade.trans _ _ (cbor_raw_serialized_iterator_match s pm i l);
      res
    }
  }
}
```
