module CBOR.Pulse.Raw.EverParse.Test
open LowParse.Spec.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Format
open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade
open LowParse.Pulse.Base
open Pulse.Lib.Slice
module SZ = FStar.SizeT

(*
```pulse
fn test (#pm: perm) (#v: Ghost.erased bytes) (s: slice byte)
  requires pts_to s #pm v ** pure (exists off . validator_success test_parse 0sz v off)
  returns _: SZ.t
  ensures pts_to s #pm v
{
  test_jump s 0sz
}
```

```pulse
fn test1 (#pm: perm) (#v: Ghost.erased bytes) (s: slice byte)
  requires pts_to s #pm v
  returns _: SZ.t
  ensures pts_to s #pm v
{
//  validate_nonempty (validate_header ()) s 0sz
//  validate_nonempty (validate_initial_byte) s 0sz
  validate_nonempty test_validate s 0sz
}
```

```pulse
fn test2 (#pm: perm) (#v: Ghost.erased initial_byte) (s: slice byte)
  requires pts_to_serialized serialize_initial_byte s  #pm v
  returns _: major_type_t
  ensures pts_to_serialized serialize_initial_byte s #pm v
{
  let x = leaf_reader_of_reader read_initial_byte s;
  x.major_type
}
```

```pulse
fn test3 (#pm: perm) (#v: Ghost.erased header) (s: slice byte)
  requires pts_to_serialized serialize_header s  #pm v
  returns _: major_type_t
  ensures pts_to_serialized serialize_header s #pm v
{
  let x = read_header () s;
  (dfst x).major_type
}
```
*)

open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format.Serialize
module U8 = FStar.UInt8

```pulse
fn ser
  (x: cbor_raw)
  (output: slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
requires
    (exists* v . cbor_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (len output)))
returns res: SZ.t
ensures
    (exists* v . cbor_match pm x y ** pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    ))
{
  cbor_serialize x output;
}
```

```pulse
fn siz
  (x: cbor_raw)
  (bound: SZ.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
requires
    (cbor_match pm x y)
returns res: SZ.t
ensures
    (cbor_match pm x y ** pure (
      cbor_size_post bound y res
    ))
{
  cbor_size x bound;
}
```
