module CBOR.Pulse.API.Det.C

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
  let res = cbor_det_mk_map () s;
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
