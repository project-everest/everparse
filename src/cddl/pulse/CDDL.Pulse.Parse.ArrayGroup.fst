module CDDL.Pulse.Parse.ArrayGroup
include CDDL.Pulse.ArrayGroup
include CDDL.Pulse.Parse.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference

let impl_zero_copy_array_group_precond
  (t: array_group None)
  (l: list cbor)
: Tot prop
= t l == Some (l, [])

let impl_zero_copy_array_group_postcond
  (#t: array_group None)
  (#tgt: Type0)
  (#tgt_size: tgt -> nat)
  (#tgt_serializable: tgt -> bool)
  (ps: array_group_parser_spec t tgt_size tgt_serializable)
  (l: list cbor)
  (v: tgt)
: Tot prop
= t l == Some (l, []) /\
  ps l == v

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_array_group
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t: array_group None)
    (#tgt: Type0)
    (#tgt_size: tgt -> nat)
    (#tgt_serializable: tgt -> bool)
    (ps: array_group_parser_spec t tgt_size tgt_serializable)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
    (pc: R.ref cbor_array_iterator_t) ->
    (#c: Ghost.erased cbor_array_iterator_t) ->
    (#p: perm) ->
    (#l: Ghost.erased (list cbor)) ->
    stt impl_tgt
        (R.pts_to pc c **
          cbor_array_iterator_match p c l **
          pure (impl_zero_copy_array_group_precond t l)
        )
        (fun res -> exists* v c' .
          r res v **
          R.pts_to pc c' **
          Trade.trade
            (r res v)
            (cbor_array_iterator_match p c l) **
          pure (impl_zero_copy_array_group_postcond ps l v)
        )

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_start: array_iterator_start_t vmatch cbor_array_iterator_match)
    (#t: Ghost.erased (array_group None))
    (#tgt: Type0)
    (#tgt_size: Ghost.erased (tgt -> nat))
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (#ps: Ghost.erased (array_group_parser_spec t tgt_size tgt_serializable))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (pa: impl_zero_copy_array_group cbor_array_iterator_match ps r)
: impl_zero_copy_parse #ty vmatch #(t_array (Ghost.reveal t)) #tgt #(spec_array_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) (parser_spec_array_group (Ghost.reveal ps) (spec_array_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable))) #impl_tgt r
=
  (c: _)
  (#p: _)
  (#v: _)
{
  let ar = cbor_array_iterator_start c;
  // BEGIN FIXME: change the type of l1 in the signature of cbor_array_iterator_start
  with pl (l1: list cbor) . assert (cbor_array_iterator_match pl ar l1);
  let l : Ghost.erased (list cbor) = Ghost.hide l1;
  Trade.rewrite_with_trade (cbor_array_iterator_match pl ar l1)
    (cbor_array_iterator_match pl ar l);
  Trade.trans _ _ (vmatch p c v);
  // END FIXME
  let mut a = ar;
  let res = pa a;
  Trade.trans _ _ (vmatch p c v);
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_item
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (#ps: Ghost.erased (parser_spec t tgt tgt_serializable))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (pa: impl_zero_copy_parse vmatch ps r)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_item (Ghost.reveal t)) #tgt #(ag_spec_item_size tgt) #(Ghost.reveal tgt_serializable) (array_group_parser_spec_item (Ghost.reveal ps) (ag_spec_item_size tgt)) #impl_tgt r
=
  (pc: _)
  (#c: _)
  (#p: _)
  (#l: _)
{
  let x = cbor_array_iterator_next pc;
  Trade.elim_hyp_r _ _ _;
  let res = pa x;
  Trade.trans _ _ (cbor_array_iterator_match p c l);
  res
}
```

module U64 = FStar.UInt64

let list_append_length_pat
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2))
  [SMTPat (List.Tot.append l1 l2)]
= List.Tot.append_length l1 l2

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_concat
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: array_iterator_share_t cbor_array_iterator_match)
  (gather: array_iterator_gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#t1: Ghost.erased (array_group None))
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
    (#t2: Ghost.erased (array_group None))
    (#tgt2: Type0)
    (#tgt_size2: Ghost.erased (tgt2 -> nat))
    (#tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#ps2: Ghost.erased (array_group_parser_spec t2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_array_group cbor_array_iterator_match ps2 r2)
    (sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_concat (Ghost.reveal t1) (Ghost.reveal t2)) #(tgt1 & tgt2) #(ag_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(ag_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (array_group_parser_spec_concat (Ghost.reveal ps1) (Ghost.reveal ps2) (ag_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (ag_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 & impl_tgt2) (rel_pair r1 r2)
=
  (pc: _)
  (#gc: _)
  (#p: _)
  (#l: _)
{
  let gl = Ghost.hide (Some?.v (Ghost.reveal t1 l));
  let gl1 = Ghost.hide (fst gl);
  let gl2 = Ghost.hide (snd gl);
  CBOR.Spec.Util.list_splitAt_append_elim gl1 gl2;
  let c0 = !pc;
  Trade.rewrite_with_trade
    (cbor_array_iterator_match p gc l)
    (cbor_array_iterator_match p c0 l); // FIXME: WHY WHY WHY? variable as head symbol
  let rlen0 = length c0;
  share c0;
  ghost fn aux (_: unit)
  requires emp ** (cbor_array_iterator_match (p /. 2.0R) c0 l ** cbor_array_iterator_match (p /. 2.0R) c0 l)
  ensures cbor_array_iterator_match p c0 l
  {
    gather c0 #(p /. 2.0R) #l #(p /. 2.0R) #l;
    rewrite (cbor_array_iterator_match (p /. 2.0R +. p /. 2.0R) c0 l)
      as (cbor_array_iterator_match p c0 l)
  };
  Trade.intro _ _ _ aux;
  Trade.trans _ _ (cbor_array_iterator_match p gc l);
  let _tmp = v1 pc;
  assert (pure (_tmp));
  with p1 gc1 l1 . assert (pts_to pc gc1 ** cbor_array_iterator_match p1 gc1 l1);
  Trade.trans_hyp_r _ _ _ _;
  let c1 = !pc;
  Trade.rewrite_with_trade (cbor_array_iterator_match p1 gc1 l1)
    (cbor_array_iterator_match p1 c1 l1);
  Trade.trans_hyp_r _ _ _ _;
  let rlen1 = length c1;
  assert (pure (U64.v rlen1 <= U64.v rlen0));
  let c0' = truncate c0 (rlen0 `U64.sub` rlen1);
  Trade.trans_hyp_l _ _ _ _;
  pc := c0';
  let w1 = pa1 pc;
  Trade.trans_hyp_l _ _ _ _;
  pc := c1;
  let w2 = pa2 pc;
  Trade.trans_hyp_r _ _ _ _;
  with z1 z2 . assert (r1 w1 z1 ** r2 w2 z2);
  let res = (w1, w2);
  Trade.rewrite_with_trade
    (r1 w1 z1 ** r2 w2 z2)
    (rel_pair r1 r2 res (z1, z2));
  Trade.trans (rel_pair r1 r2 res (z1, z2)) _ _;
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_array_group_choice
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#t1: Ghost.erased (array_group None))
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (array_group_parser_spec t1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_array_group cbor_array_iterator_match ps1 r1)
    (v1: impl_array_group cbor_array_iterator_match t1)
    (#t2: Ghost.erased (array_group None))
    (#tgt2: Type0)
    (#tgt_size2: Ghost.erased (tgt2 -> nat))
    (#tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#ps2: Ghost.erased (array_group_parser_spec t2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_array_group cbor_array_iterator_match ps2 r2)
: impl_zero_copy_array_group #cbor_array_iterator_t cbor_array_iterator_match #(array_group_choice (Ghost.reveal t1) (Ghost.reveal t2)) #(tgt1 `either` tgt2) #(ag_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(ag_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (array_group_parser_spec_choice (Ghost.reveal ps1) (Ghost.reveal ps2) (ag_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (ag_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 `either` impl_tgt2) (rel_either r1 r2)
=
  (pc: _)
  (#gc: _)
  (#p: _)
  (#l: _)
{
  let c0 = !pc;
  let test1 = v1 pc;
  Trade.elim _ _;
  pc := c0;
  if (test1) {
    let w1 = pa1 pc;
    with z1 . assert (r1 w1 z1);
    let res : either impl_tgt1 impl_tgt2 = Inl w1;
    Trade.rewrite_with_trade (r1 w1 z1) (rel_either r1 r2 res (Inl z1));
    Trade.trans _ (r1 w1 z1) _;
    res
  } else {
    let w2 = pa2 pc;
    with z2 . assert (r2 w2 z2);
    let res : either impl_tgt1 impl_tgt2 = Inr w2;
    Trade.rewrite_with_trade (r2 w2 z2) (rel_either r1 r2 res (Inr z2));
    Trade.trans _ (r2 w2 z2) _;
    res
  }
}
```
