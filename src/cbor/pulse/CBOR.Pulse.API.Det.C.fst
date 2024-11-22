module CBOR.Pulse.API.Det.C
include CBOR.Pulse.API.Det.Common
open Pulse.Lib.Pervasives
open CBOR.Spec.Constants

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

```pulse
fn cbor_det_mk_string_from_array
  (ty: major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to a #p v ** pure (
      Seq.length v == U64.v len /\
      (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
    ))
returns res: cbor_det_t
ensures
    (exists* p' v' .
      cbor_det_match p' res (Spec.pack (Spec.CString ty v')) **
      Trade.trade
        (cbor_det_match p' res (Spec.pack (Spec.CString ty v')))
        (pts_to a #p v) **
      pure (Ghost.reveal v == v')
    )
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
fn cbor_det_mk_array_from_array
  (a: A.array cbor_det_t)
  (len: U64.t)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbor_det_t))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
requires
    (A.pts_to a #pa va **
      PM.seq_list_match va vv (cbor_det_match pv) **
      pure (A.length a == U64.v len)
    )
returns res: cbor_det_t
ensures
    (exists* p' v' .
      cbor_det_match p' res (Spec.pack (Spec.CArray v')) **
      Trade.trade
        (cbor_det_match p' res (Spec.pack (Spec.CArray v')))
        (A.pts_to a #pa va **
          PM.seq_list_match va vv (cbor_det_match pv)
        ) **
        pure (Ghost.reveal vv == v')
    )
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
fn cbor_det_mk_map_from_array
  (a: A.array cbor_det_map_entry_t)
  (len: U64.t)
  (#va: Ghost.erased (Seq.seq cbor_det_map_entry_t))
  (#pv: perm)
  (#vv: Ghost.erased (list (Spec.cbor & Spec.cbor)))
requires
    (A.pts_to a va **
      PM.seq_list_match va vv (cbor_det_map_entry_match pv) **
      pure (A.length a == U64.v len /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)
      )
    )
returns res: cbor_det_t
ensures
    (exists* p' v' va' .
      cbor_det_match p' res (Spec.pack (Spec.CMap v')) **
      Trade.trade
        (cbor_det_match p' res (Spec.pack (Spec.CMap v')))
        (A.pts_to a va' **
          PM.seq_list_match va vv (cbor_det_map_entry_match pv)
        ) **
        pure (
          (forall x . List.Tot.assoc x vv == Spec.cbor_map_get v' x) /\
          Spec.cbor_map_length v' == Seq.length va
        )
    )
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
