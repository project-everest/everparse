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
  CBOR.Spec.Raw.Format.cbor_compare

[@@noextract_to "krml"] noextract
let spec_cbor_map_entry_raw_compare
  (x1 x2: CBOR.Spec.Raw.Base.raw_data_item & CBOR.Spec.Raw.Base.raw_data_item)
: Tot int
= CBOR.Spec.Raw.Format.cbor_compare (fst x1) (fst x2)

```pulse
fn cbor_map_entry_raw_compare
  (p: perm)
: Pulse.Lib.Array.MergeSort.impl_compare_t u#0 u#0 #_ #_ (Raw.cbor_match_map_entry p) spec_cbor_map_entry_raw_compare
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

assume val cbor_raw_sort_aux (p: perm) : Pulse.Lib.Array.MergeSort.sort_aux_t #_ #_ (Raw.cbor_match_map_entry p) spec_cbor_map_entry_raw_compare // Pulse issue here

let cbor_raw_sort
  (p: perm)
: Pulse.Lib.Array.MergeSort.sort_t #_ #_ (Raw.cbor_match_map_entry p) spec_cbor_map_entry_raw_compare
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
  admit ()
}
```

let spec_cbor_map_entry_raw_compare_correct : squash (
  let order = (CBOR.Spec.Raw.Valid.map_entry_order CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order _) in
  let compare = spec_cbor_map_entry_raw_compare in
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))
  )
= admit ()

let list_sorted_ext_eq_map_entry_order_deterministically_encoded_cbor_map_key_order
  (l1 l2: list (CBOR.Spec.Raw.Base.raw_data_item & CBOR.Spec.Raw.Base.raw_data_item))
: Lemma
  (requires (
    let order = CBOR.Spec.Raw.Valid.map_entry_order CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order CBOR.Spec.Raw.Base.raw_data_item in
    List.Tot.sorted order l1 == true /\
    True (* /\
    List.Tot.sorted order l2 == true /\
 (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2)
*) 
  ))
  (ensures (
    l1 == l2
  ))
= admit () (*
CBOR.Spec.Util.list_sorted_ext_eq
    (CBOR.Spec.Raw.Valid.map_entry_order CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order _)
    l1 l2
*)

assume val cbor_map_sort_correct
  (l l': list (CBOR.Spec.Raw.Base.raw_data_item & CBOR.Spec.Raw.Base.raw_data_item))
: Lemma
  (requires List.Tot.no_repeats_p (List.Tot.map fst l) /\
    l' == CBOR.Spec.Raw.Sort.cbor_map_sort l
  )
  (ensures (
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l')) /\
    List.Tot.sorted (CBOR.Spec.Raw.Valid.map_entry_order CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order _) l' /\
    (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
  ))

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
  assert (SM.seq_list_match va vv1 (Raw.cbor_match_map_entry pv));
  let _ : bool = cbor_raw_sort pv a (SZ.uint64_to_sizet len);
  Trade.trans _ _ (SM.seq_list_match va vv (cbor_det_map_entry_match pv));
  with va' vv' . assert (Pulse.Lib.Array.pts_to a va' ** SM.seq_list_match va' vv' (Raw.cbor_match_map_entry pv));
  A.pts_to_len a;
  SM.seq_list_match_length (Raw.cbor_match_map_entry pv) va' vv';
  cbor_map_sort_correct vv1 (CBOR.Spec.Raw.Sort.cbor_map_sort vv1);
  Pulse.Lib.Array.MergeSort.spec_sort_correct
    (CBOR.Spec.Raw.Valid.map_entry_order CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order _)
    spec_cbor_map_entry_raw_compare
    vv1;
  assume (pure (
    List.Tot.sorted
      (CBOR.Spec.Raw.Valid.map_entry_order CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order _)
      vv'
  ));
  assert (pure (
    forall x . List.Tot.memP x vv' <==> List.Tot.memP x (CBOR.Spec.Raw.Sort.cbor_map_sort vv1)
  ));
  list_sorted_ext_eq_map_entry_order_deterministically_encoded_cbor_map_key_order
    vv'
    (CBOR.Spec.Raw.Sort.cbor_map_sort vv1);
  let raw_len = CBOR.Spec.Raw.Valid.mk_raw_uint64 len;
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
