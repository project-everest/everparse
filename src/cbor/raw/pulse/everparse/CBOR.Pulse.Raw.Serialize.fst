module CBOR.Pulse.Raw.Serialize
open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Spec.Raw.Order
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base

open CBOR.Pulse.Raw.Match
module LP = LowParse.Pulse.Combinators

assume val ser_body
  (f: (p: perm) -> LP.l2r_writer (cbor_match p) serialize_raw_data_item)
  (p: perm)
: LP.l2r_writer (cbor_match p) serialize_raw_data_item

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

let ser_pre
  (p: perm)
  (x': cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
: Tot slprop
=
    (S.pts_to out v ** cbor_match p x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize serialize_raw_data_item x) <= Seq.length v
    ))

let ser_post
  (p: perm)
  (x': cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
  (res: SZ.t)
: Tot slprop
=
  exists* v' .
      S.pts_to out v' ** cbor_match p x' x ** pure (
      let bs = bare_serialize serialize_raw_data_item x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bs
  )

inline_for_extraction
```pulse
fn ser_fold
  (f: (p: perm) -> (x': cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre p x' x out offset v) (fun res -> ser_post p x' x out offset v res))
  (p: perm)
: LP.l2r_writer #cbor_raw #raw_data_item (cbor_match p) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': cbor_raw) (#x: raw_data_item) (out: S.slice LP.byte) (offset: SZ.t) (#v: Ghost.erased LP.bytes)
{
  fold (ser_pre p x' x out offset v);
  let res = f p x' x out offset v;
  unfold (ser_post p x' x out offset v res);
  res
}
```

inline_for_extraction
```pulse
fn ser_unfold
  (f: (p: perm) -> LP.l2r_writer (cbor_match p) serialize_raw_data_item)
  (p: perm)
  (x': cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre p x' x out offset v)
returns res: SZ.t
ensures
  (ser_post p x' x out offset v res)
{
  unfold (ser_pre p x' x out offset v);
  let res = f p x' out offset;
  fold (ser_post p x' x out offset v res);
  res
}
```

inline_for_extraction
```pulse
fn ser_body'
  (f: (p: perm) -> (x': cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre p x' x out offset v) (fun res -> ser_post p x' x out offset v res))
  (p: perm)
  (x': cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre p x' x out offset v)
returns res: SZ.t
ensures
  ser_post p x' x out offset v res
{
  ser_unfold (ser_fold f) p x' x out offset v;
}
```

inline_for_extraction
```pulse
fn rec ser'
  (p: perm)
  (x': cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre p x' x out offset v)
returns res: SZ.t
ensures
  ser_post p x' x out offset v res
{
  ser_body' ser' p x' x out offset v
}
```

let ser (p: perm) : l2r_writer (cbor_match p) serialize_raw_data_item = ser_fold ser' p
