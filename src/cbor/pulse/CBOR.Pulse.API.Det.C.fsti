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

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_string_from_array_t =
  (ty: major_type_byte_string_or_text_string) ->
  (a: A.array U8.t) ->
  (len: U64.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_det_t
    (pts_to a #p v ** pure (
      Seq.length v == U64.v len /\
      (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
    ))
    (fun res -> exists* p' v' .
      cbor_det_match p' res v' **
      Trade.trade
        (cbor_det_match p' res v')
        (pts_to a #p v) **
      pure (
        Spec.CString? (Spec.unpack v') /\
        Ghost.reveal v == Spec.CString?.v (Spec.unpack v')
      )
    )

val cbor_det_mk_string_from_array (_: unit) : cbor_det_mk_string_from_array_t

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_array_from_array_t =
  (a: A.array cbor_det_t) ->
  (len: U64.t) ->
  (#pa: perm) ->
  (#va: Ghost.erased (Seq.seq cbor_det_t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list Spec.cbor)) ->
  stt cbor_det_t
    (A.pts_to a #pa va **
      PM.seq_list_match va vv (cbor_det_match pv) **
      pure (A.length a == U64.v len)
    )
    (fun res -> exists* p' v' .
      cbor_det_match p' res v' **
      Trade.trade
        (cbor_det_match p' res v')
        (A.pts_to a #pa va **
          PM.seq_list_match va vv (cbor_det_match pv)
        ) **
        pure (
          Spec.CArray? (Spec.unpack v') /\
          Ghost.reveal vv == Spec.CArray?.v (Spec.unpack v')
        )
    )

val cbor_det_mk_array_from_array (_: unit) : cbor_det_mk_array_from_array_t

inline_for_extraction
noextract [@@noextract_to "krml"]
```pulse
fn cbor_det_mk_array_from_array'
  (a: A.array cbor_det_t)
  (len: U64.t)
  (va0: Ghost.erased (Seq.seq cbor_det_t))
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbor_det_t))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
requires
    (A.pts_to a #pa va **
      PM.seq_list_match va0 vv (cbor_det_match pv) **
      pure (A.length a == U64.v len /\
        Seq.equal va0 va
      )
    )
returns res: cbor_det_t
ensures
    (exists* p' v' .
      cbor_det_match p' res v' **
      Trade.trade
        (cbor_det_match p' res v')
        (A.pts_to a #pa va **
          PM.seq_list_match va0 vv (cbor_det_match pv)
        ) **
        pure (
          Spec.CArray? (Spec.unpack v') /\
          Ghost.reveal vv == Spec.CArray?.v (Spec.unpack v')
        )
    )
{
  Trade.rewrite_with_trade
    (PM.seq_list_match va0 vv (cbor_det_match pv))
    (PM.seq_list_match va vv (cbor_det_match pv));
  let res = cbor_det_mk_array_from_array () a len;
  Trade.trans_concl_r _ _ _ (PM.seq_list_match va0 vv (cbor_det_match pv));
  res
}
```

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_map_from_array_t =
  (a: A.array cbor_det_map_entry_t) ->
  (len: U64.t) ->
  (#va: Ghost.erased (Seq.seq cbor_det_map_entry_t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (Spec.cbor & Spec.cbor))) ->
  stt cbor_det_t
    (A.pts_to a va **
      PM.seq_list_match va vv (cbor_det_map_entry_match pv) **
      pure (A.length a == U64.v len /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)
      )
    )
    (fun res -> exists* p' v' va' .
      cbor_det_match p' res v' **
      Trade.trade
        (cbor_det_match p' res v')
        (A.pts_to a va' **
          PM.seq_list_match va vv (cbor_det_map_entry_match pv)
        ) **
        pure (
          Spec.CMap? (Spec.unpack v') /\
          (forall x . List.Tot.assoc x vv == Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack v')) x) /\
          Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack v')) == Seq.length va
        )
    )

val cbor_det_mk_map_from_array (_: unit) : cbor_det_mk_map_from_array_t

inline_for_extraction
noextract [@@noextract_to "krml"]
```pulse
fn cbor_det_mk_map_from_array'
  (a: A.array cbor_det_map_entry_t)
  (len: U64.t)
  (va0: Ghost.erased (Seq.seq cbor_det_map_entry_t))
  (#va: Ghost.erased (Seq.seq cbor_det_map_entry_t))
  (#pv: perm)
  (#vv: Ghost.erased (list (Spec.cbor & Spec.cbor)))
requires
    (A.pts_to a va **
      PM.seq_list_match va0 vv (cbor_det_map_entry_match pv) **
      pure (A.length a == U64.v len /\
        List.Tot.no_repeats_p (List.Tot.map fst vv) /\
        Seq.equal va0 va
      )
    )
returns res: cbor_det_t
ensures
    (exists* p' v' va' .
      cbor_det_match p' res v' **
      Trade.trade
        (cbor_det_match p' res v')
        (A.pts_to a va' **
          PM.seq_list_match va0 vv (cbor_det_map_entry_match pv)
        ) **
        pure (
          Spec.CMap? (Spec.unpack v') /\
          (forall x . List.Tot.assoc x vv == Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack v')) x) /\
          Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack v')) == Seq.length va
        )
    )
{
  Trade.rewrite_with_trade
    (PM.seq_list_match va0 vv (cbor_det_map_entry_match pv))
    (PM.seq_list_match va vv (cbor_det_map_entry_match pv));
  let res = cbor_det_mk_map_from_array () a len;
  Trade.trans_concl_r _ _ _ (PM.seq_list_match va0 vv (cbor_det_map_entry_match pv));
  res
}
```
