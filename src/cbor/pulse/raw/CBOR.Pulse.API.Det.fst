module CBOR.Pulse.API.Det
friend CBOR.Pulse.API.Det.Type
friend CBOR.Spec.API.Format

module SpecRaw = CBOR.Spec.Raw
module Raw = CBOR.Pulse.Raw.Match
module SM = Pulse.Lib.SeqMatch.Util
module Compare = CBOR.Pulse.Raw.Compare
module Parse = CBOR.Pulse.Raw.Format.Parse
module Serialize = CBOR.Pulse.Raw.Format.Serialize

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

let cbor_det_validate_post_intro
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Lemma
  (requires (Parse.cbor_validate_det_post v res))
  (ensures (cbor_det_validate_post v res))
= Classical.forall_intro (Classical.move_requires SpecRaw.mk_det_raw_cbor_mk_cbor);
  assert (forall (v1: SpecRaw.raw_data_item) . (SpecRaw.raw_data_item_ints_optimal v1 /\ SpecRaw.raw_data_item_sorted SpecRaw.deterministically_encoded_cbor_map_key_order v1) ==> SpecRaw.serialize_cbor v1 == Spec.cbor_det_serialize (SpecRaw.mk_cbor v1))

```pulse
fn cbor_det_validate
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v)
returns res: SZ.t
ensures
    (pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))
{
  let res = Parse.cbor_validate_det input;
  cbor_det_validate_post_intro v res;
  res
}
```

let cbor_det_parse_aux
  (v: Seq.seq U8.t)
  (len: nat)
  (v1': SpecRaw.raw_data_item {
    len <= Seq.length v /\
    Seq.slice v 0 (len) == SpecRaw.serialize_cbor v1'
  })
  (v1: Spec.cbor)
  (v2: Seq.seq U8.t)
: Lemma
  (v == Spec.cbor_det_serialize v1 `Seq.append` v2 ==> v1' == SpecRaw.mk_det_raw_cbor v1)
= Seq.lemma_split v len;
  Classical.move_requires (SpecRaw.serialize_cbor_inj (SpecRaw.mk_det_raw_cbor v1) v1' v2) (Seq.slice v (len) (Seq.length v))

```pulse
fn cbor_det_parse
  (input: S.slice U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    ))
returns res: cbor_det_t
ensures
    (exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == Spec.cbor_det_serialize v'
    ))
{
  Seq.lemma_split v (SZ.v len);
  let res = Parse.cbor_parse input len;
  with v1' . assert (Raw.cbor_match 1.0R res v1');
  Classical.forall_intro_2 (cbor_det_parse_aux v (SZ.v len) v1');
  fold (cbor_det_match 1.0R res (SpecRaw.mk_cbor v1'));
  res
}
```

```pulse
fn cbor_det_size
  (x: cbor_det_t)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (cbor_det_match pm x y)
returns res: SZ.t
ensures
    (cbor_det_match pm x y ** pure (
      cbor_det_size_post bound y res
    ))
{
  unfold (cbor_det_match pm x y);
  let res = Serialize.cbor_size x bound;
  fold (cbor_det_match pm x y);
  res
}
```

```pulse
fn cbor_det_serialize
  (x: cbor_det_t)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (Seq.length (Spec.cbor_det_serialize y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      let s = Spec.cbor_det_serialize y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    ))
{
  unfold (cbor_det_match pm x y);
  let res = Serialize.cbor_serialize x output;
  fold (cbor_det_match pm x y);
  res
}
```

```pulse
fn cbor_det_mk_simple_value (_: unit) : mk_simple_t u#0 #_ cbor_det_match
= (v: _)
{
  let res = Raw.cbor_match_simple_intro v;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CSimple v)));
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CSimple v)));
  res
}
```

```pulse
fn cbor_det_mk_int64 (_: unit) : mk_int64_t u#0 #_ cbor_det_match
= (ty: _)
  (v: _)
{
  let res = Raw.cbor_match_int_intro ty (SpecRaw.mk_raw_uint64 v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CInt64 ty v)));
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CInt64 ty v)));
  res
}
```

```pulse
fn cbor_det_mk_string (_: unit) : mk_string_t u#0 #_ cbor_det_match
= (ty: _)
  (s: _)
  (#p: _)
  (#v: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  let len64 = SpecRaw.mk_raw_uint64 (SZ.sizet_to_uint64 (S.len s));
  let res = Raw.cbor_match_string_intro ty len64 s;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CString ty v)));
  SpecRaw.mk_cbor_eq (SpecRaw.String ty len64 v);
  SpecRaw.mk_cbor_equiv (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CString ty v))) (SpecRaw.String ty len64 v);
  assert (pure (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CString ty v)) `SpecRaw.raw_equiv` SpecRaw.String ty len64 v));
  SpecRaw.raw_equiv_sorted_optimal
    SpecRaw.deterministically_encoded_cbor_map_key_order
    (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CString ty v)))
    (SpecRaw.String ty len64 v);
  assert (pure (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CString ty v)) == SpecRaw.String ty len64 v));
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CString ty v)));
  res
}
```

```pulse
fn cbor_det_mk_tagged (_: unit) : mk_tagged_t #_ cbor_det_match
= (tag: _)
  (r: _)
  (#pr: _)
  (#v: _)
  (#pv: _)
  (#v': _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let tag64 = SpecRaw.mk_raw_uint64 tag;
  let w' : Ghost.erased SpecRaw.raw_data_item = SpecRaw.mk_det_raw_cbor v';
  Trade.rewrite_with_trade
    (cbor_det_match pv v v')
    (Raw.cbor_match pv v w');
  let res = Raw.cbor_match_tagged_intro tag64 r;
  Trade.trans_concl_r _ _ (Raw.cbor_match pv v w') _;
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v')));
  SpecRaw.mk_cbor_eq (SpecRaw.Tagged tag64 w');
  SpecRaw.mk_cbor_equiv (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v'))) (SpecRaw.Tagged tag64 w');
  assert (pure (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v')) `SpecRaw.raw_equiv` SpecRaw.Tagged tag64 w'));
  SpecRaw.raw_equiv_sorted_optimal
    SpecRaw.deterministically_encoded_cbor_map_key_order
    (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v')))
    (SpecRaw.Tagged tag64 w');
  assert (pure (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CTagged tag v')) == SpecRaw.Tagged tag64 w'));
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CTagged tag v')));
  res
}
```

noextract [@@noextract_to "krml"]
let mk_det_raw_cbor (c: Spec.cbor) : Tot SpecRaw.raw_data_item = // FIXME: WHY WHY WHY do I need that? Pulse cannot typecheck `Pure _ True (fun _ -> _)` functions into `Tot` functions
  SpecRaw.mk_det_raw_cbor c

```pulse
ghost
fn rec seq_list_array_cbor_det_match_elim
  (p: perm)
  (c: Seq.seq cbor_det_t)
  (v: list (Spec.cbor))
requires
  SM.seq_list_match c v (cbor_det_match p)
ensures
  SM.seq_list_match c (List.Tot.map mk_det_raw_cbor v) (Raw.cbor_match p) **
  Trade.trade
    (SM.seq_list_match c (List.Tot.map mk_det_raw_cbor v) (Raw.cbor_match p))
    (SM.seq_list_match c v (cbor_det_match p))
decreases v
{
  SM.seq_list_match_length (cbor_det_match p) c v;
  if (Nil? v) {
    SM.seq_list_match_nil_elim c v (cbor_det_match p);
    SM.seq_list_match_nil_intro c (List.Tot.map mk_det_raw_cbor v) (Raw.cbor_match p);
    ghost fn aux (_: unit)
      requires emp ** SM.seq_list_match c (List.Tot.map mk_det_raw_cbor v) (Raw.cbor_match p)
      ensures SM.seq_list_match c v (cbor_det_match p)
    {
      SM.seq_list_match_nil_elim c (List.Tot.map mk_det_raw_cbor v) (Raw.cbor_match p);
      SM.seq_list_match_nil_intro c v (cbor_det_match p);
    };
    Trade.intro _ _ _ aux
  } else {
    SM.seq_list_match_cons_elim_trade c v (cbor_det_match p);
    Trade.rewrite_with_trade
      (cbor_det_match p (Seq.head c) (List.Tot.hd v))
      (Raw.cbor_match p (Seq.head c) (mk_det_raw_cbor (List.Tot.hd v)));
    Trade.trans_hyp_l _ _ _ (SM.seq_list_match c v (cbor_det_match p));
    seq_list_array_cbor_det_match_elim p (Seq.tail c) (List.Tot.tl v);
    Trade.trans_hyp_r _ _ _ (SM.seq_list_match c v (cbor_det_match p));
    SM.seq_list_match_cons_intro_trade (Seq.head c) (mk_det_raw_cbor (List.Tot.hd v)) (Seq.tail c) (List.Tot.map mk_det_raw_cbor (List.Tot.tl v)) (Raw.cbor_match p);
    Trade.trans _ _ (SM.seq_list_match c v (cbor_det_match p));
  }
}
```

let rec list_map_mk_det_raw_cbor_correct
  (l: list Spec.cbor)
: Lemma
  (ensures (
    let l' = List.Tot.map mk_det_raw_cbor l in
    List.Tot.for_all SpecRaw.raw_data_item_ints_optimal l' /\
    List.Tot.for_all (SpecRaw.raw_data_item_sorted SpecRaw.deterministically_encoded_cbor_map_key_order) l'
  ))
  [SMTPat (List.Tot.map mk_det_raw_cbor l)]
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_det_raw_cbor_correct q

let rec list_map_mk_cbor_mk_det_raw_cbor
  (l: list Spec.cbor)
: Lemma
  (ensures (
    List.Tot.map SpecRaw.mk_cbor (List.Tot.map mk_det_raw_cbor l) == l
  ))
  [SMTPat (List.Tot.map mk_det_raw_cbor l)]
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_cbor_mk_det_raw_cbor q

```pulse
fn cbor_det_mk_array (_: unit) : mk_array_t #_ cbor_det_match
= (a: _)
  (len: _)
  (#pa: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  A.pts_to_len a;
  SM.seq_list_match_length (cbor_det_match pv) va vv;
  let len64 = SpecRaw.mk_raw_uint64 len;
  let vv1 = Ghost.hide (List.Tot.map mk_det_raw_cbor vv);
  let v' : Ghost.erased Spec.cbor = Ghost.hide (Spec.pack (Spec.CArray vv));
  seq_list_array_cbor_det_match_elim _ _ _;
  let _ : squash (SpecRaw.raw_data_item_ints_optimal == SpecRaw.holds_on_raw_data_item SpecRaw.raw_data_item_ints_optimal_elem) = assert_norm (SpecRaw.raw_data_item_ints_optimal == SpecRaw.holds_on_raw_data_item SpecRaw.raw_data_item_ints_optimal_elem);
  let _ : squash (SpecRaw.raw_data_item_sorted SpecRaw.deterministically_encoded_cbor_map_key_order == SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order)) = assert_norm (SpecRaw.raw_data_item_sorted SpecRaw.deterministically_encoded_cbor_map_key_order == SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order));
  SpecRaw.raw_data_item_sorted_optimal_valid SpecRaw.deterministically_encoded_cbor_map_key_order (SpecRaw.Array len64 vv1);
  SpecRaw.mk_cbor_eq (SpecRaw.Array len64 vv1);
  SpecRaw.mk_det_raw_cbor_mk_cbor (SpecRaw.Array len64 vv1);
  let res = Raw.cbor_match_array_intro len64 a;
  Trade.trans_concl_r _ _ _ _;
  Spec.unpack_pack (Spec.CArray vv);
  fold (cbor_det_match 1.0R res (Spec.pack (Spec.CArray vv)));
  res
}
```

let cbor_det_map_entry_match p c v =
  Raw.cbor_match_map_entry p c (SpecRaw.mk_det_raw_cbor (fst v), SpecRaw.mk_det_raw_cbor (snd v))

```pulse
fn cbor_raw_compare (p: perm) : Pulse.Lib.Array.MergeSort.impl_compare_t u#0 u#0 #_ #_
  (Raw.cbor_match p)
  SpecRaw.cbor_compare
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  Compare.impl_cbor_compare x1 x2
}
```

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

```pulse
fn rec cbor_raw_sort_aux
  (p: perm)
  (a: A.array Raw.cbor_map_entry)
  (lo: SZ.t)
  (hi: SZ.t)
  (#c: Ghost.erased (Seq.seq Raw.cbor_map_entry))
  (#l: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
requires
  A.pts_to_range a (SZ.v lo) (SZ.v hi) c **
  SM.seq_list_match c l (Raw.cbor_match_map_entry p)
returns res: bool
ensures
  Pulse.Lib.Array.MergeSort.sort_aux_post (Raw.cbor_match_map_entry p) SpecRaw.cbor_map_entry_raw_compare a lo hi c l res
{
  Pulse.Lib.Array.MergeSort.sort_aux
    (Raw.cbor_match_map_entry p)
    SpecRaw.cbor_map_entry_raw_compare
    (cbor_map_entry_raw_compare p)
    (cbor_raw_sort_aux p)
    a lo hi
}
```

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
