module CBOR.Pulse.API.Det.C

(* NOTE: this .fst file does not need anything from the Raw namespace,
but it has been moved here to be hidden from verified clients. *)

```pulse
fn cbor_det_validate
  (input: AP.ptr U8.t)
  (input_len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (SZ.v input_len == Seq.length v))
returns res: SZ.t
ensures
    (pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))
{
  let s = SU.arrayptr_to_slice_intro_trade input input_len;
  let res = CBOR.Pulse.API.Det.Common.cbor_det_validate s;
  Trade.elim _ (pts_to input #pm v);
  res
}
```

module ID = FStar.IndefiniteDescription

let cbor_det_validate_success_elim
  (len: SZ.t)
  (v: Seq.seq U8.t)
: Pure (Ghost.erased (Spec.cbor & Seq.seq U8.t))
    (requires exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1))
    (ensures fun (v1, v2) ->
      Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    )
= let p v1 v2 = Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1) in
  assert (exists v1 v2 . p v1 v2);
  let v1 = FStar.IndefiniteDescription.indefinite_description_tot _ (fun v1 -> exists v2 . p v1 v2) in
  assert (exists v2 . p v1 v2);
  let v2 = FStar.IndefiniteDescription.indefinite_description_tot _ (fun v2 -> p v1 v2) in
  (Ghost.reveal v1, Ghost.reveal v2)

```pulse
fn cbor_det_parse
  (input: AP.ptr U8.t)
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
  let v1v2 = cbor_det_validate_success_elim len v;
  assert (pure (Seq.equal (Seq.slice v 0 (SZ.v len)) (Spec.cbor_det_serialize (fst v1v2))));
  let gr : Ghost.erased (AP.ptr U8.t) = AP.ghost_split input len;
  ghost fn aux (_: unit)
  requires pts_to (Ghost.reveal gr) #pm (Seq.slice v (SZ.v len) (Seq.length v)) ** pts_to input #pm (Seq.slice v 0 (SZ.v len))
  ensures pts_to input #pm v
  {
    Seq.lemma_split v (SZ.v len);
    AP.join input gr
  };
  Trade.intro _ _ _ aux;
  Seq.append_empty_r (Spec.cbor_det_serialize (fst v1v2));
  let s = SU.arrayptr_to_slice_intro_trade input len;
  Trade.trans _ _ (pts_to input #pm v);
  S.pts_to_len s;
  let res = CBOR.Pulse.API.Det.Common.cbor_det_parse s;
  Trade.trans _ _ (pts_to input #pm v);
  res
}
```

#restart-solver
```pulse
fn cbor_det_serialize
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      SZ.v output_len == Seq.length v /\
      cbor_det_serialize_postcond y res v
    ))
{
  let ou = S.arrayptr_to_slice_intro output output_len;
  S.pts_to_len ou;
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize x ou;
  S.pts_to_len ou;
  assert (pure (SZ.v res == Seq.length (Spec.cbor_det_serialize y)));
  S.arrayptr_to_slice_elim ou;
  res
}
```

```pulse
fn cbor_det_mk_string_from_array (_: unit) : cbor_det_mk_string_from_array_t
=
  (ty: major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  A.pts_to_len a;
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  ghost fn aux (_: unit)
    requires S.is_from_array a s ** pts_to s #p v
    ensures A.pts_to a #p v
  {
    S.to_array s;
  };
  Trade.intro _ _ _ aux;
  S.pts_to_len s;
  let res = cbor_det_mk_string () ty s;
  with p' v' . assert (cbor_det_match p' res (Spec.pack (Spec.CString ty v')));
  Trade.trans (cbor_det_match p' res (Spec.pack (Spec.CString ty v'))) _ _;
  res
}
```

```pulse
fn cbor_det_mk_array_from_array (_: unit) : cbor_det_mk_array_from_array_t
=
  (a: A.array cbor_det_t)
  (len: U64.t)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbor_det_t))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
{
  A.pts_to_len a;
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  ghost fn aux (_: unit)
    requires S.is_from_array a s ** pts_to s #pa va
    ensures A.pts_to a #pa va
  {
    S.to_array s;
  };
  Trade.intro _ _ _ aux;
  Trade.reg_r (pts_to s #pa va) (A.pts_to a #pa va) (PM.seq_list_match va vv (cbor_det_match pv));
  S.pts_to_len s;
  let res = cbor_det_mk_array () s;
  with p' v' . assert (cbor_det_match p' res (Spec.pack (Spec.CArray v')));
  Trade.trans (cbor_det_match p' res (Spec.pack (Spec.CArray v'))) _ _;
  res
}
```

```pulse
fn cbor_det_mk_map_from_array (_: unit) : cbor_det_mk_map_from_array_t
=
  (a: A.array cbor_det_map_entry_t)
  (len: U64.t)
  (#va: Ghost.erased (Seq.seq cbor_det_map_entry_t))
  (#pv: perm)
  (#vv: Ghost.erased (list (Spec.cbor & Spec.cbor)))
{
  A.pts_to_len a;
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  S.pts_to_len s;
  let res = CBOR.Pulse.API.Base.mk_map_from_ref (CBOR.Pulse.API.Det.Type.dummy_cbor_det_t ()) (CBOR.Pulse.API.Det.Common.cbor_det_mk_map_gen ()) s;
  with p' v' va' . assert (
      Trade.trade
        (cbor_det_match p' res (Spec.pack (Spec.CMap v')))
        (pts_to s va' **
          PM.seq_list_match va vv (cbor_det_map_entry_match pv)
        )
  );
  ghost fn aux (_: unit)
    requires S.is_from_array a s ** pts_to s va'
    ensures A.pts_to a va'
  {
    S.to_array s;
  };
  Trade.intro _ _ _ aux;
  Trade.reg_r (pts_to s va') (A.pts_to a va') (PM.seq_list_match va vv (cbor_det_map_entry_match pv));
  Trade.trans (cbor_det_match p' res (Spec.pack (Spec.CMap v'))) _ _;
  res
}
```

```pulse
fn cbor_det_get_string
  (_: unit)
: cbor_det_get_string_t
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let sl = CBOR.Pulse.API.Det.Common.cbor_det_get_string () x;
  let res = SU.slice_to_arrayptr_intro_trade sl;
  Trade.trans _ _ (cbor_det_match p x y);
  res
}
```

```pulse
fn cbor_det_map_get
  (_: unit)
: map_get_by_ref_t #_ cbor_det_match
=
  (x: _)
  (k: _)
  (dest: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
  (#vdest0: _)
{
  CBOR.Pulse.API.Det.Common.cbor_det_map_get () x k dest
}
```
