module CBOR.Pulse.API.Det
friend CBOR.Pulse.API.Det.Type
friend CBOR.Spec.API.Format

module SpecRaw = CBOR.Spec.Raw
module Raw = CBOR.Pulse.Raw.Match
module SM = Pulse.Lib.SeqMatch.Util

let cbor_det_match
  p c v
= Raw.cbor_match p c (SpecRaw.mk_det_raw_cbor v)

let cbor_det_match_with_size
  sz p c v
= cbor_det_match p c v ** pure (sz == Seq.length (Spec.cbor_det_serialize v))

```pulse
ghost
fn cbor_det_match_with_size_eq
  (sz: nat)
  (p: perm)
  (c: cbor_det_t)
  (v: Spec.cbor)
requires
    (cbor_det_match_with_size sz p c v)
ensures
    (cbor_det_match_with_size sz p c v **
      pure (sz == Seq.length (Spec.cbor_det_serialize v))
    )
{
    unfold (cbor_det_match_with_size sz p c v);
    fold (cbor_det_match_with_size sz p c v)
}
```

let cbor_det_map_entry_match p c v =
  Raw.cbor_match_map_entry p c (SpecRaw.mk_det_raw_cbor (fst v), SpecRaw.mk_det_raw_cbor (snd v))

assume val cbor_raw_compare (p: perm) : Pulse.Lib.Array.MergeSort.impl_compare_t
  (Raw.cbor_match p)
  SpecRaw.cbor_compare

```pulse
fn cbor_map_entry_raw_compare
  (p: perm)
: Pulse.Lib.Array.MergeSort.impl_compare_t u#0 u#0 #_ #_ (Raw.cbor_match_map_entry p) SpecRaw.cbor_map_entry_raw_compare
= (x1: _)
  (x2: _)
  (#y1: _)
  (#y2: _)
{
  unfold (Raw.cbor_match_map_entry p x1 y1);
  unfold (Raw.cbor_match_map_entry p x2 y2);
  let res = cbor_raw_compare p x1.cbor_map_entry_key x2.cbor_map_entry_key;
  fold (Raw.cbor_match_map_entry p x1 y1);
  fold (Raw.cbor_match_map_entry p x2 y2);
  res
}
```

assume val cbor_raw_sort_aux (p: perm) : Pulse.Lib.Array.MergeSort.sort_aux_t #_ #_ (Raw.cbor_match_map_entry p) SpecRaw.cbor_map_entry_raw_compare // Pulse issue here

let cbor_raw_sort
  (p: perm)
: Pulse.Lib.Array.MergeSort.sort_t #_ #_ (Raw.cbor_match_map_entry p) SpecRaw.cbor_map_entry_raw_compare
= Pulse.Lib.Array.MergeSort.sort _ _ (cbor_raw_sort_aux p)

```pulse
ghost
fn rec seq_list_map_cbor_det_map_entry_match_elim
  (p: perm)
  (c: Seq.seq cbor_det_map_entry_t)
  (v: list (Spec.cbor & Spec.cbor))
requires
  SM.seq_list_match c v (cbor_det_map_entry_match p)
ensures
  SM.seq_list_match c (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry v) (Raw.cbor_match_map_entry p) **
  Trade.trade
    (SM.seq_list_match c (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry v) (Raw.cbor_match_map_entry p))
    (SM.seq_list_match c v (cbor_det_map_entry_match p))
decreases v
{
  SM.seq_list_match_length (cbor_det_map_entry_match p) c v;
  if (Nil? v) {
    SM.seq_list_match_nil_elim c v (cbor_det_map_entry_match p);
    SM.seq_list_match_nil_intro c (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry v) (Raw.cbor_match_map_entry p);
    ghost fn aux (_: unit)
      requires emp ** SM.seq_list_match c (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry v) (Raw.cbor_match_map_entry p)
      ensures SM.seq_list_match c v (cbor_det_map_entry_match p)
    {
      SM.seq_list_match_nil_elim c (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry v) (Raw.cbor_match_map_entry p);
      SM.seq_list_match_nil_intro c v (cbor_det_map_entry_match p);
    };
    Trade.intro _ _ _ aux
  } else {
    SM.seq_list_match_cons_elim_trade c v (cbor_det_map_entry_match p);
    Trade.rewrite_with_trade
      (cbor_det_map_entry_match p (Seq.head c) (List.Tot.hd v))
      (Raw.cbor_match_map_entry p (Seq.head c) (SpecRaw.mk_det_raw_cbor_map_entry (List.Tot.hd v)));
    Trade.trans_hyp_l _ _ _ (SM.seq_list_match c v (cbor_det_map_entry_match p));
    seq_list_map_cbor_det_map_entry_match_elim p (Seq.tail c) (List.Tot.tl v);
    Trade.trans_hyp_r _ _ _ (SM.seq_list_match c v (cbor_det_map_entry_match p));
    SM.seq_list_match_cons_intro_trade (Seq.head c) (SpecRaw.mk_det_raw_cbor_map_entry (List.Tot.hd v)) (Seq.tail c) (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry (List.Tot.tl v)) (Raw.cbor_match_map_entry p);
    Trade.trans _ _ (SM.seq_list_match c v (cbor_det_map_entry_match p));
  }
}
```

```pulse
fn cbor_det_mk_map
  (_: unit)
: mk_map_t u#0 #cbor_det_t #cbor_det_map_entry_t cbor_det_match cbor_det_map_entry_match
= (a: _)
  (len: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  A.pts_to_len a;
  SM.seq_list_match_length (cbor_det_map_entry_match pv) va vv;
  let vv1 = Ghost.hide (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry vv);
  let v' : Ghost.erased Spec.cbor = Ghost.hide (SpecRaw.mk_det_raw_cbor_map vv len);
  seq_list_map_cbor_det_map_entry_match_elim pv va vv;
  let _ : bool = cbor_raw_sort pv a (SZ.uint64_to_sizet len);
  Trade.trans _ _ (SM.seq_list_match va vv (cbor_det_map_entry_match pv));
  with va' vv' . assert (Pulse.Lib.Array.pts_to a va' ** SM.seq_list_match va' vv' (Raw.cbor_match_map_entry pv));
  A.pts_to_len a;
  SM.seq_list_match_length (Raw.cbor_match_map_entry pv) va' vv';
  SpecRaw.cbor_map_sort_correct vv1;
  Pulse.Lib.Array.MergeSort.spec_sort_correct
    (SpecRaw.map_entry_order SpecRaw.deterministically_encoded_cbor_map_key_order _)
    SpecRaw.cbor_map_entry_raw_compare
    vv1;
  SpecRaw.cbor_map_entry_raw_compare_succeeds vv1;
  CBOR.Spec.Util.list_sorted_ext_eq
    (SpecRaw.map_entry_order SpecRaw.deterministically_encoded_cbor_map_key_order _)
    vv'
    (SpecRaw.cbor_map_sort vv1);
  let raw_len = SpecRaw.mk_raw_uint64 len;
  let res = CBOR.Pulse.Raw.Match.cbor_match_map_intro raw_len a;
  Trade.trans_concl_r _ _ _ (SM.seq_list_match va vv (cbor_det_map_entry_match pv));
  with p' vraw . assert (Raw.cbor_match p' res vraw);
  SpecRaw.pack_unpack v';
  Trade.rewrite_with_trade
    (Raw.cbor_match p' res vraw)
    (cbor_det_match p' res (SpecRaw.pack (SpecRaw.CMap (SpecRaw.CMap?.c (SpecRaw.unpack v')))));
  Trade.trans (cbor_det_match p' res (SpecRaw.pack (SpecRaw.CMap (SpecRaw.CMap?.c (SpecRaw.unpack v'))))) _ _;
  res
}
```
