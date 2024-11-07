module CBOR.Pulse.API.Det
friend CBOR.Pulse.API.Det.Type
friend CBOR.Spec.API.Format

module SpecRaw = CBOR.Spec.Raw
module Raw = CBOR.Pulse.Raw.Match
module SM = Pulse.Lib.SeqMatch.Util
module Compare = CBOR.Pulse.Raw.Compare
module Parse = CBOR.Pulse.Raw.Format.Parse
module Serialize = CBOR.Pulse.Raw.Format.Serialize
module Read = CBOR.Pulse.Raw.Read
module Map = CBOR.Spec.Raw.Map

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

```pulse
fn cbor_det_equal (_: unit) : equal_t u#0 #_ cbor_det_match
= (x1: _)
  (x2: _)
  (#p1: _)
  (#p2: _)
  (#v1: _)
  (#v2: _)
{
  Classical.move_requires (SpecRaw.mk_det_raw_cbor_inj v1) v2;
  SpecRaw.cbor_compare_equal (SpecRaw.mk_det_raw_cbor v1) (SpecRaw.mk_det_raw_cbor v2);
  unfold (cbor_det_match p1 x1 v1);
  unfold (cbor_det_match p2 x2 v2);
  let comp = Compare.impl_cbor_compare x1 x2;
  fold (cbor_det_match p1 x1 v1);
  fold (cbor_det_match p2 x2 v2);
  (comp = 0s)
}
```

```pulse
fn cbor_det_major_type (_: unit) : get_major_type_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Compare.impl_major_type x;
  fold (cbor_det_match p x v);
  res
}
```

```pulse
fn cbor_det_read_simple_value (_: unit) : read_simple_value_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Raw.cbor_match_simple_elim x;
  fold (cbor_det_match p x v);
  res
}
```

```pulse
fn cbor_det_read_uint64 (_: unit) : read_uint64_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Raw.cbor_match_int_elim_value x;
  fold (cbor_det_match p x v);
  res.value
}
```

```pulse
fn cbor_det_get_string (_: unit) : get_string_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  Trade.rewrite_with_trade
    (cbor_det_match p x v)
    (Raw.cbor_match p x (SpecRaw.mk_det_raw_cbor v));
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Raw.cbor_match_string_elim_payload x;
  Trade.trans _ _ (cbor_det_match p x v);
  res
}
```

```pulse
fn cbor_det_get_tagged_tag (_: unit) : get_tagged_tag_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Raw.cbor_match_tagged_get_tag x;
  fold (cbor_det_match p x v);
  res.value
}
```

```pulse
fn cbor_det_get_tagged_payload (_: unit) : get_tagged_payload_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  Trade.rewrite_with_trade
    (cbor_det_match p x v)
    (Raw.cbor_match p x (SpecRaw.mk_det_raw_cbor v));
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Read.cbor_match_tagged_get_payload x;
  Trade.trans _ _ (cbor_det_match p x v);
  with p' v' . assert (Raw.cbor_match p' res v');
  SpecRaw.mk_det_raw_cbor_mk_cbor v';
  Trade.rewrite_with_trade
    (Raw.cbor_match p' res v')
    (cbor_det_match p' res (SpecRaw.mk_cbor v'));
  Trade.trans _ _ (cbor_det_match p x v);
  res
}
```

```pulse
fn cbor_det_get_array_length (_: unit) : get_array_length_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Raw.cbor_match_array_get_length x;
  fold (cbor_det_match p x v);
  res.value
}
```

let cbor_det_array_iterator_match
  (p: perm)
  (i: cbor_det_array_iterator_t)
  (l: list Spec.cbor)
: Tot slprop
= Read.cbor_array_iterator_match p i (List.Tot.map mk_det_raw_cbor l)

let rec list_map_mk_det_raw_cbor_mk_cbor
  (l: list SpecRaw.raw_data_item)
: Lemma
  (requires (
    List.Tot.for_all (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem)) l /\
    List.Tot.for_all (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order)) l
  ))
  (ensures (
    List.Tot.map mk_det_raw_cbor (List.Tot.map SpecRaw.mk_cbor l) == l
  ))
  [SMTPat (List.Tot.map SpecRaw.mk_cbor l)]
= match l with
  | [] -> ()
  | a :: q ->
    SpecRaw.mk_det_raw_cbor_mk_cbor a;
    list_map_mk_det_raw_cbor_mk_cbor q

```pulse
fn cbor_det_array_iterator_start (_: unit) : array_iterator_start_t u#0 u#0 #_ #_ cbor_det_match cbor_det_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  Trade.rewrite_with_trade
    (cbor_det_match p x v)
    (Raw.cbor_match p x (SpecRaw.mk_det_raw_cbor v));
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_array_iterator_init f64 x;
  Trade.trans _ _ (cbor_det_match p x v);
  with p' l . assert (Read.cbor_array_iterator_match p' res l);
  list_map_mk_det_raw_cbor_mk_cbor l;
  Trade.rewrite_with_trade
    (Read.cbor_array_iterator_match p' res l)
    (cbor_det_array_iterator_match p' res (List.Tot.map SpecRaw.mk_cbor l));
  Trade.trans _ _ (cbor_det_match p x v);
  res
}
```

```pulse
fn cbor_det_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_det_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_array_iterator_match p x v);
  let res = Read.cbor_array_iterator_is_empty x;
  fold (cbor_det_array_iterator_match p x v);
  res
}
```

```pulse
fn cbor_det_array_iterator_next (_: unit) : array_iterator_next_t u#0 #_ #_ cbor_det_match cbor_det_array_iterator_match
= (x: _)
  (#y: _)
  (#py: _)
  (#z: _)
{
  Trade.rewrite_with_trade
    (cbor_det_array_iterator_match py y z)
    (Read.cbor_array_iterator_match py y (List.Tot.map mk_det_raw_cbor z));
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_array_iterator_next f64 x;
  Trade.trans _ _ (cbor_det_array_iterator_match py y z);
  with y' z' . assert (Read.cbor_array_iterator_match py y' z');
  Trade.rewrite_with_trade
    (Read.cbor_array_iterator_match py y' z')
    (cbor_det_array_iterator_match py y' (List.Tot.tl z));
  Trade.trans_hyp_r _ _ _ (cbor_det_array_iterator_match py y z);
  with p' v' . assert (Raw.cbor_match p' res v');
  Trade.rewrite_with_trade
    (Raw.cbor_match p' res v')
    (cbor_det_match p' res (List.Tot.hd z));
  Trade.trans_hyp_l _ _ _ (cbor_det_array_iterator_match py y z);
  res
}
```

let rec list_index_map
  (#t1 #t2: Type)
  (f: (t1 -> t2))
  (l: list t1)
  (i: nat)
: Lemma
  (requires (i < List.Tot.length l))
  (ensures (
    let l' = List.Tot.map f l in
    i < List.Tot.length l' /\
    List.Tot.index l' i == f (List.Tot.index l i)
  ))
  [SMTPat (List.Tot.index (List.Tot.map f l) i)]
= if i = 0
  then ()
  else list_index_map f (List.Tot.tl l) (i - 1)

```pulse
fn cbor_det_get_array_item (_: unit) : get_array_item_t u#0 #_ cbor_det_match
= (x: _)
  (i: _)
  (#p: _)
  (#v: _)
{
  let l : Ghost.erased (list Spec.cbor) = Ghost.hide (Spec.CArray?.v (Spec.unpack v));
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  Trade.rewrite_with_trade
    (cbor_det_match p x v)
    (Raw.cbor_match p x (SpecRaw.mk_det_raw_cbor v));
  let res = Read.cbor_array_item (assume (SZ.fits_u64)) x i;
  Trade.trans _ _ (cbor_det_match p x v);
  with p' v' . assert (Raw.cbor_match p' res v');
  list_map_mk_cbor_mk_det_raw_cbor l;
  assert (pure (List.Tot.index (List.Tot.map SpecRaw.mk_cbor (List.Tot.map mk_det_raw_cbor l)) (U64.v i) == List.Tot.index l (U64.v i)));
  Trade.rewrite_with_trade
    (Raw.cbor_match p' res v')
    (cbor_det_match p' res (List.Tot.index l (U64.v i)));
  Trade.trans _ _ (cbor_det_match p x v);
  res
}
```

```pulse
fn cbor_det_get_map_length (_: unit) : get_map_length_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p x v);
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor v);
  let res = Raw.cbor_match_map_get_length x;
  fold (cbor_det_match p x v);
  res.value
}
```

let cbor_det_map_iterator_match
  (p: perm)
  (i: cbor_det_map_iterator_t)
  (l: list (Spec.cbor & Spec.cbor))
: Tot slprop
= Read.cbor_map_iterator_match p i (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry l)

noextract [@@noextract_to "krml"]
let mk_cbor_map_entry
  (l: (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
: Tot (Spec.cbor & Spec.cbor)
= (SpecRaw.mk_cbor (fst l), SpecRaw.mk_cbor (snd l))

let rec mk_cbor_match_map_elem_elim_aux
  (r: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
  (x: Spec.cbor)
: Lemma
  (requires (
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) r /\
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) r
  ))
  (ensures (
    match List.Tot.assoc x (List.Tot.map mk_cbor_map_entry r), List.Tot.assoc (SpecRaw.mk_det_raw_cbor x) r with
    | None, None -> True
    | Some v1, Some v2 -> v2 = SpecRaw.mk_det_raw_cbor v1
    | _ -> False
  ))
  (decreases r)
= match r with
  | [] -> ()
  | (k, v) :: q ->
    SpecRaw.mk_det_raw_cbor_mk_cbor k;
    SpecRaw.mk_det_raw_cbor_mk_cbor v;
    mk_cbor_match_map_elem_elim_aux q x

let mk_cbor_match_map_elem_elim'
  (r: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
  (m: Spec.cbor_map)
  (x: Spec.cbor)
: Lemma
  (requires (
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) r /\
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) r /\
    SpecRaw.mk_cbor_match_map r m
  ))
  (ensures (
    List.Tot.assoc x (List.Tot.map mk_cbor_map_entry r) == Spec.cbor_map_get m x
  ))
= assert (SpecRaw.mk_cbor_match_map_elem r m (SpecRaw.mk_det_raw_cbor x));
  let _ : squash (SpecRaw.raw_data_item_ints_optimal == SpecRaw.holds_on_raw_data_item SpecRaw.raw_data_item_ints_optimal_elem) = assert_norm (SpecRaw.raw_data_item_ints_optimal == SpecRaw.holds_on_raw_data_item SpecRaw.raw_data_item_ints_optimal_elem) in
  let _ : squash (SpecRaw.raw_data_item_sorted SpecRaw.deterministically_encoded_cbor_map_key_order == SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order)) = assert_norm (SpecRaw.raw_data_item_sorted SpecRaw.deterministically_encoded_cbor_map_key_order == SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order)) in
  SpecRaw.list_setoid_assoc_sorted_optimal SpecRaw.deterministically_encoded_cbor_map_key_order (SpecRaw.mk_det_raw_cbor x) r;
  mk_cbor_match_map_elem_elim_aux r x

let mk_cbor_match_map_elim
  (r: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
  (m: Spec.cbor_map)
: Lemma
  (requires (
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) r /\
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) r /\
    SpecRaw.mk_cbor_match_map r m
  ))
  (ensures (
    forall (x: Spec.cbor) . List.Tot.assoc x (List.Tot.map mk_cbor_map_entry r) == Spec.cbor_map_get m x
  ))
= Classical.forall_intro (Classical.move_requires (mk_cbor_match_map_elem_elim' r m))

let rec mk_cbor_match_map_elem_elim_no_repeats_p
  (r: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) r /\
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) r /\
    List.Tot.sorted (SpecRaw.map_entry_order SpecRaw.deterministically_encoded_cbor_map_key_order _) r
  ))
  (ensures (
    List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.map mk_cbor_map_entry r))
  ))
  (decreases r)
= match r with
  | [] -> ()
  | (k, v) :: q ->
    mk_cbor_match_map_elem_elim_no_repeats_p q;
    let prf () : Lemma
      (requires (List.Tot.memP (SpecRaw.mk_cbor k) (List.Tot.map fst (List.Tot.map mk_cbor_map_entry q))))
      (ensures False)
    = let x = CBOR.Spec.Util.list_memP_map_elim fst (SpecRaw.mk_cbor k) (List.Tot.map mk_cbor_map_entry q) in
      let y = CBOR.Spec.Util.list_memP_map_elim mk_cbor_map_entry x q in
      assert (SpecRaw.mk_cbor k == SpecRaw.mk_cbor (fst y));
      List.Tot.for_all_mem (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) q;
      List.Tot.for_all_mem (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) q;
      CBOR.Spec.Util.list_sorted_memP (SpecRaw.map_entry_order SpecRaw.deterministically_encoded_cbor_map_key_order _) (k, v) q y;
      SpecRaw.mk_det_raw_cbor_mk_cbor k;
      SpecRaw.mk_det_raw_cbor_mk_cbor (fst y);
      assert False
    in
    Classical.move_requires prf ()

let rec list_map_mk_det_raw_cbor_map_entry_mk_cbor_map_entry
  (r: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) r /\
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) r
  ))
  (ensures (
    List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry (List.Tot.map mk_cbor_map_entry r) == r
  ))
  (decreases r)
= match r with
  | [] -> ()
  | (k, v) :: q ->
    SpecRaw.mk_det_raw_cbor_mk_cbor k;
    SpecRaw.mk_det_raw_cbor_mk_cbor v;
    list_map_mk_det_raw_cbor_map_entry_mk_cbor_map_entry q

let cbor_det_order
  (x1 x2: Spec.cbor)
: Tot bool
= SpecRaw.deterministically_encoded_cbor_map_key_order (SpecRaw.mk_det_raw_cbor x1) (SpecRaw.mk_det_raw_cbor x2)

let cbor_det_compare
  (x1 x2: Spec.cbor)
: Tot int
= SpecRaw.cbor_compare (SpecRaw.mk_det_raw_cbor x1) (SpecRaw.mk_det_raw_cbor x2)

let cbor_det_compare_swap
  (x1 x2: Spec.cbor)
: Lemma
  (cbor_det_compare x1 x2 < 0 <==> cbor_det_compare x2 x1 > 0)
= let x1' = SpecRaw.mk_det_raw_cbor x1 in
  let x2' = SpecRaw.mk_det_raw_cbor x2 in
  SpecRaw.cbor_compare_correct x1' x2';
  SpecRaw.cbor_compare_correct x2' x1';
  SpecRaw.bytes_lex_compare_opp (SpecRaw.serialize_cbor x2') (SpecRaw.serialize_cbor x1')

let cbor_det_compare_equal
  (x1 x2: Spec.cbor)
: Lemma
  (cbor_det_compare x1 x2 == 0 <==> x1 == x2)
= SpecRaw.cbor_compare_equal (SpecRaw.mk_det_raw_cbor x1) (SpecRaw.mk_det_raw_cbor x2)

let cbor_det_order_eq
  (x1 x2: Spec.cbor)
: Lemma
  (cbor_det_order x1 x2 <==> (cbor_det_compare x1 x2 < 0))
= SpecRaw.cbor_compare_correct (SpecRaw.mk_det_raw_cbor x1) (SpecRaw.mk_det_raw_cbor x2);
SpecRaw.deterministically_encoded_cbor_map_key_order_spec (SpecRaw.mk_det_raw_cbor x1) (SpecRaw.mk_det_raw_cbor x2)

module U = CBOR.Spec.Util

let cbor_det_order_irrefl : squash (U.order_irrefl cbor_det_order) = ()

let cbor_det_order_trans : squash (U.order_trans cbor_det_order) = ()

module I16 = FStar.Int16

```pulse
fn impl_cbor_det_compare
  (x1: cbor_det_t)
  (x2: cbor_det_t)
  (#px1: perm)
  (#px2: perm)
  (#vx1: Ghost.erased Spec.cbor)
  (#vx2: Ghost.erased Spec.cbor)
requires (cbor_det_match px1 x1 vx1 ** cbor_det_match px2 x2 vx2)
returns res: I16.t
ensures cbor_det_match px1 x1 vx1 ** cbor_det_match px2 x2 vx2 ** pure (Compare.same_sign (I16.v res) (cbor_det_compare vx1 vx2))
{
  unfold (cbor_det_match px1 x1 vx1);
  unfold (cbor_det_match px2 x2 vx2);
  let res = Compare.impl_cbor_compare x1 x2;
  fold (cbor_det_match px1 x1 vx1);
  fold (cbor_det_match px2 x2 vx2);
  res
}
```

let rec list_sorted_map_mk_cbor_map_entry
  (r: list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_ints_optimal_elem))) r /\
    List.Tot.for_all (CBOR.Spec.Util.holds_on_pair (SpecRaw.holds_on_raw_data_item (SpecRaw.raw_data_item_sorted_elem SpecRaw.deterministically_encoded_cbor_map_key_order))) r /\
    List.Tot.sorted (SpecRaw.map_entry_order SpecRaw.deterministically_encoded_cbor_map_key_order _) r
  ))
  (ensures (
    List.Tot.sorted (SpecRaw.map_entry_order cbor_det_order _) (List.Tot.map mk_cbor_map_entry r)
  ))
  (decreases r)
= match r with
  | [] -> ()
  | [_] -> ()
  | (k1, v1) :: (k2, v2) :: q ->
    SpecRaw.mk_det_raw_cbor_mk_cbor k1;
    SpecRaw.mk_det_raw_cbor_mk_cbor k2;
    list_sorted_map_mk_cbor_map_entry ((k2, v2) :: q)

let det_map_iterator_start_post
  (y: Spec.cbor)
  (l' : list (Spec.cbor & Spec.cbor))
: Tot prop
= match Spec.unpack y with
      | Spec.CMap l -> (forall k . Spec.cbor_map_get l k == List.Tot.assoc k l') /\
        List.Tot.length l' == Spec.cbor_map_length l /\
        List.Tot.no_repeats_p (List.Tot.map fst l') /\
        List.Tot.sorted (SpecRaw.map_entry_order cbor_det_order _) l'
      | _ -> False

inline_for_extraction
let det_map_iterator_start_t
= (x: cbor_det_t) ->
  (#p: perm) ->
  (#y: Ghost.erased Spec.cbor) ->
  stt cbor_det_map_iterator_t
    (cbor_det_match p x y ** pure (Spec.CMap? (Spec.unpack y)))
    (fun res -> exists* p' l' .
      cbor_det_map_iterator_match p' res l' **
      Trade.trade
        (cbor_det_map_iterator_match p' res l')
        (cbor_det_match p x y) **
      pure (
        det_map_iterator_start_post y l'
    ))

```pulse
fn cbor_det_map_iterator_start' (_: unit) : det_map_iterator_start_t
= (x: _)
  (#p: _)
  (#y: _)
{
  Trade.rewrite_with_trade
    (cbor_det_match p x y)
    (Raw.cbor_match p x (SpecRaw.mk_det_raw_cbor y));
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor y);
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_map_iterator_init f64 x;
  Trade.trans _ _ (cbor_det_match p x y);
  with p' l . assert (Read.cbor_map_iterator_match p' res l);
  list_map_mk_det_raw_cbor_map_entry_mk_cbor_map_entry l;  
  mk_cbor_match_map_elem_elim_no_repeats_p l;
  list_sorted_map_mk_cbor_map_entry l;
  let m : Ghost.erased Spec.cbor_map = Spec.CMap?.c (Spec.unpack y);
  mk_cbor_match_map_elim l m;
  Trade.rewrite_with_trade
    (Read.cbor_map_iterator_match p' res l)
    (cbor_det_map_iterator_match p' res (List.Tot.map mk_cbor_map_entry l));
  Trade.trans _ _ (cbor_det_match p x y);
  res
}
```

```pulse
fn cbor_det_map_iterator_start (_: unit) : map_iterator_start_t u#0 u#0 #_ #_ cbor_det_match cbor_det_map_iterator_match
= (x: _)
  (#p: _)
  (#y: _)
{
  cbor_det_map_iterator_start' () x;
}
```

```pulse
fn cbor_det_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_det_map_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_map_iterator_match p x v);
  let res = Read.cbor_map_iterator_is_empty x;
  fold (cbor_det_map_iterator_match p x v);
  res
}
```

```pulse
fn cbor_det_map_iterator_next (_: unit) : map_iterator_next_t u#0 #_ #_ cbor_det_map_entry_match cbor_det_map_iterator_match
= (x: _)
  (#y: _)
  (#py: _)
  (#z: _)
{
  Trade.rewrite_with_trade
    (cbor_det_map_iterator_match py y z)
    (Read.cbor_map_iterator_match py y (List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry z));
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_map_iterator_next f64 x;
  Trade.trans _ _ (cbor_det_map_iterator_match py y z);
  with y' z' . assert (Read.cbor_map_iterator_match py y' z');
  Trade.rewrite_with_trade
    (Read.cbor_map_iterator_match py y' z')
    (cbor_det_map_iterator_match py y' (List.Tot.tl z));
  Trade.trans_hyp_r _ _ _ (cbor_det_map_iterator_match py y z);
  with p' v' . assert (Raw.cbor_match_map_entry p' res v');
  Trade.rewrite_with_trade
    (Raw.cbor_match_map_entry p' res v')
    (cbor_det_map_entry_match p' res (List.Tot.hd z));
  Trade.trans_hyp_l _ _ _ (cbor_det_map_iterator_match py y z);
  res
}
```

```pulse
fn cbor_det_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_det_map_entry_match cbor_det_match
= (x2: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_det_map_entry_match p x2 v2);
  unfold (Raw.cbor_match_map_entry p x2 (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
  fold (cbor_det_match p x2.cbor_map_entry_key (fst v2));
  ghost fn aux (_: unit)
    requires Raw.cbor_match p x2.cbor_map_entry_value (SpecRaw.mk_det_raw_cbor (snd v2)) ** cbor_det_match p x2.cbor_map_entry_key (fst v2)
    ensures cbor_det_map_entry_match p x2 v2
  {
    unfold (cbor_det_match p x2.cbor_map_entry_key (fst v2));
    fold (Raw.cbor_match_map_entry p x2 (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
    fold (cbor_det_map_entry_match p x2 v2);
  };
  Trade.intro _ _ _ aux;
  x2.cbor_map_entry_key
}
```

```pulse
fn cbor_det_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_det_map_entry_match cbor_det_match
= (x2: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_det_map_entry_match p x2 v2);
  unfold (Raw.cbor_match_map_entry p x2 (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
  fold (cbor_det_match p x2.cbor_map_entry_value (snd v2));
  ghost fn aux (_: unit)
    requires Raw.cbor_match p x2.cbor_map_entry_key (SpecRaw.mk_det_raw_cbor (fst v2)) ** cbor_det_match p x2.cbor_map_entry_value (snd v2)
    ensures cbor_det_map_entry_match p x2 v2
  {
    unfold (cbor_det_match p x2.cbor_map_entry_value (snd v2));
    fold (Raw.cbor_match_map_entry p x2 (SpecRaw.mk_det_raw_cbor (fst v2), SpecRaw.mk_det_raw_cbor (snd v2)));
    fold (cbor_det_map_entry_match p x2 v2);
  };
  Trade.intro _ _ _ aux;
  x2.cbor_map_entry_value
}
```

let cbor_det_map_get_invariant_none
  (b: bool)
  (px: perm)
  (x: cbor_det_t)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (m: Spec.cbor_map)
  (p': perm)
  (i: cbor_det_map_iterator_t)
: Tot slprop
= exists* l .
    cbor_det_map_iterator_match p' i l **
    Trade.trade
      (cbor_det_map_iterator_match p' i l)
      (cbor_det_match px x vx) **
  pure (
    List.Tot.sorted (SpecRaw.map_entry_order cbor_det_order _) l /\
    Spec.cbor_map_get m vk == (if b then List.Tot.assoc vk l else None) /\
    (b ==> Cons? l)
  )

let cbor_det_map_get_invariant_some
  (px: perm)
  (x: cbor_det_t)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (m: Spec.cbor_map)
  (x': cbor_det_t)
: Tot slprop
= exists* p' vx' .
    cbor_det_match p' x' vx' **
    Trade.trade
      (cbor_det_match p' x' vx')
      (cbor_det_match px x vx) **
    pure (
      Spec.cbor_map_get m vk == Some vx'
    )

let cbor_det_map_get_invariant
  (b: bool)
  (px: perm)
  (x: cbor_det_t)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (m: Spec.cbor_map)
  (p': perm)
  (i: cbor_det_map_iterator_t)
  (res: option cbor_det_t)
: Tot slprop
= match res with
  | None -> cbor_det_map_get_invariant_none b px x vx vk m p' i
  | Some x' -> cbor_det_map_get_invariant_some px x vx vk m x'

let cbor_det_map_get_invariant_false_elim_precond
  (vx: Spec.cbor)
  (m: Spec.cbor_map)
: Tot prop
= match Spec.unpack vx with
  | Spec.CMap m' -> m == m'
  | _ -> False

```pulse
ghost
fn cbor_det_map_get_invariant_false_elim
  (px: perm)
  (x: cbor_det_t)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (m: Spec.cbor_map)
  (p' : perm)
  (i: cbor_det_map_iterator_t)
  (res: option cbor_det_t)
requires
  cbor_det_map_get_invariant false px x vx vk m p' i res **
  pure (cbor_det_map_get_invariant_false_elim_precond vx m)
ensures
  map_get_post cbor_det_match x px vx vk res **
  pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
{
  match res {
    None -> {
      unfold (cbor_det_map_get_invariant false px x vx vk m p' i None);
      unfold (cbor_det_map_get_invariant_none false px x vx vk m p' i);
      Trade.elim _ _;
      fold (map_get_post_none cbor_det_match x px vx vk);
      fold (map_get_post cbor_det_match x px vx vk res)
    }
    Some x' -> {
      unfold (cbor_det_map_get_invariant false px x vx vk m p' i (Some x'));
      unfold (cbor_det_map_get_invariant_some px x vx vk m x');
      fold (map_get_post_some cbor_det_match x px vx vk x');
      fold (map_get_post cbor_det_match x px vx vk res)
    }
  }
}
```

```pulse
fn cbor_det_map_get (_: unit)
: map_get_t u#0 #_ cbor_det_match
= (x: _)
  (k: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
{
  let m : Ghost.erased Spec.cbor_map = Ghost.hide (Spec.CMap?.c (Spec.unpack vx));
  let i = cbor_det_map_iterator_start' () x;
  with p' l . assert (cbor_det_map_iterator_match p' i l);
  let mut pi = i;
  let mut pres = None #cbor_det_t;
  let i_is_empty = cbor_det_map_iterator_is_empty () i;
  let cont = not i_is_empty;
  let mut pcont = cont;
  fold (cbor_det_map_get_invariant_none cont px x vx vk m p' i);
  fold (cbor_det_map_get_invariant cont px x vx vk m p' i None);
  while (
    !pcont
  ) invariant cont . exists* i res .
    pts_to pi i **
    pts_to pcont cont **
    pts_to pres res **
    cbor_det_match pk k vk **
    cbor_det_map_get_invariant cont px x vx vk m p' i res **
    pure (cont ==> None? res)
  {
    with gb gi gres . assert (cbor_det_map_get_invariant gb px x vx vk m p' gi gres);
    unfold (cbor_det_map_get_invariant gb px x vx vk m p' gi None);
    unfold (cbor_det_map_get_invariant_none gb px x vx vk m p' gi);
    let entry = cbor_det_map_iterator_next () pi;
    Trade.trans _ _ (cbor_det_match px x vx);
    with pentry ventry . assert (cbor_det_map_entry_match pentry entry ventry);
    let key = cbor_det_map_entry_key () entry;
    let comp = impl_cbor_det_compare key k;
    Trade.elim _ (cbor_det_map_entry_match pentry entry ventry);
    cbor_det_compare_equal (fst ventry) vk;
    with gi' l' . assert (cbor_det_map_iterator_match p' gi' l');
    if (comp = 0s) {
      Trade.elim_hyp_r _ _ (cbor_det_match px x vx);
      let value = cbor_det_map_entry_value () entry;
      Trade.trans _ _ (cbor_det_match px x vx);
      pres := Some value;
      pcont := false;
      fold (cbor_det_map_get_invariant_some px x vx vk m value);
      fold (cbor_det_map_get_invariant false px x vx vk m p' gi' (Some value))
    } else if (I16.gt comp 0s) {
      Trade.elim_hyp_l _ _ (cbor_det_match px x vx);
      cbor_det_compare_swap vk (fst ventry);
      cbor_det_order_eq vk (fst ventry);
      Classical.move_requires (Map.list_sorted_map_entry_order_lt_tail cbor_det_order ventry l') vk;
      List.Tot.assoc_mem (Ghost.reveal vk) l';
      pcont := false;
      fold (cbor_det_map_get_invariant_none false px x vx vk m p' gi');
      fold (cbor_det_map_get_invariant false px x vx vk m p' gi' None);
    } else {
      Trade.elim_hyp_l _ _ (cbor_det_match px x vx);
      let i' = !pi;
      Trade.rewrite_with_trade (cbor_det_map_iterator_match p' gi' l')
        (cbor_det_map_iterator_match p' i' l');
      Trade.trans _ _ (cbor_det_match px x vx);
      let is_empty = cbor_det_map_iterator_is_empty () i';
      let cont = not is_empty;
      pcont := cont;
      fold (cbor_det_map_get_invariant_none cont px x vx vk m p' i');
      fold (cbor_det_map_get_invariant cont px x vx vk m p' i' None);
    }
  };
  with gb gi gres . assert (cbor_det_map_get_invariant gb px x vx vk m p' gi gres);
  cbor_det_map_get_invariant_false_elim px x vx vk m p' gi gres;
  !pres
}
```
