module CBOR.Pulse.Raw.Copy
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box

[@@erasable]
noeq
type freeable_tree = // this is necessary to define the freeable slprop by structural recursion, because freeable_cbor' is not structurally recursive because V.vec and B.box may introduce cycles
| FTBytes
| FTBox: (b: freeable_tree) -> freeable_tree
| FTArray: (a: list freeable_tree) -> freeable_tree
| FTMap: (m: list (freeable_tree & freeable_tree)) -> freeable_tree
| FTUnit

noeq
type freeable_cbor' =
| FBytes: (v: V.vec U8.t) -> freeable_cbor'
| FBox: (b: freeable_cbor_box) -> freeable_cbor'
| FArray: (a: freeable_cbor_array) -> freeable_cbor'
| FMap: (m: freeable_cbor_map) -> freeable_cbor'
| FUnit

and freeable_cbor_box = {
  box_cbor: B.box cbor_raw; // the box turned into ref in cbor_tagged
  box_footprint: B.box freeable_cbor'; // the freeable_cbor associated to the contents of box_cbor
}

and freeable_cbor_array = {
  array_cbor: V.vec cbor_raw; // the vec turned into slice in cbor_array
  array_footprint: V.vec freeable_cbor'; // the freeable_cbor objects associated to each element of array_cbor
  array_len: (array_len: SZ.t { SZ.v array_len == V.length array_footprint });
}

and freeable_cbor_map_entry = {
  map_entry_key: freeable_cbor';
  map_entry_value: freeable_cbor';
}

and freeable_cbor_map = {
  map_cbor: V.vec cbor_map_entry; // the vec turned into slice in cbor_map
  map_footprint: V.vec freeable_cbor_map_entry; // the freeable_cbor objects associated to each map entry key and value of map_cbor
  map_len: (map_len: SZ.t { SZ.v map_len == V.length map_footprint });
}

module SM = Pulse.Lib.SeqMatch

let rec freeable_match'
  (x: freeable_cbor')
  (ft: freeable_tree)
: Tot slprop
  (decreases ft)
= match x, ft with
  | FBytes ve, FTBytes -> exists* (v: Seq.seq U8.t) . pts_to ve v ** pure (V.is_full_vec ve)
  | FBox bx, FTBox ft' -> exists* (v: cbor_raw) (x': freeable_cbor') . pts_to bx.box_cbor v ** pts_to bx.box_footprint x' ** freeable_match' x' ft'
  | FArray ar, FTArray ft' -> exists* (v: Seq.seq cbor_raw) (x': Seq.seq freeable_cbor') . pts_to ar.array_cbor v ** pts_to ar.array_footprint x' ** SM.seq_list_match x' ft' freeable_match' ** pure (V.is_full_vec ar.array_cbor /\ V.is_full_vec ar.array_footprint)
  | FMap m, FTMap ft' -> exists* (v: Seq.seq cbor_map_entry) (x': Seq.seq freeable_cbor_map_entry) . pts_to m.map_cbor v ** pts_to m.map_footprint x' ** SM.seq_list_match x' ft' (freeable_match_map_entry' ft freeable_match') ** pure (V.is_full_vec m.map_cbor /\ V.is_full_vec m.map_footprint)
  | FUnit, FTUnit -> emp
  | _ -> pure False
    
and freeable_match_map_entry'
  (r0: freeable_tree)
  (freeable_match: (freeable_cbor' -> (v': freeable_tree { v' << r0 }) -> slprop))
  (c: freeable_cbor_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
: Tot slprop
  (decreases r)
= freeable_match' c.map_entry_key (fst r) **
  freeable_match' c.map_entry_value (snd r)

let freeable_match_map_entry
  (c: freeable_cbor_map_entry)
  (r: (freeable_tree & freeable_tree))
: Tot slprop
  (decreases r)
= freeable_match' c.map_entry_key (fst r) **
  freeable_match' c.map_entry_value (snd r)

```pulse
ghost
fn freeable_match_map_entry_weaken
  (r0: freeable_tree)
  (c: freeable_cbor_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_map_entry' r0 freeable_match' c r
ensures
  freeable_match_map_entry c r
{
  unfold (freeable_match_map_entry' r0 freeable_match' c r);
  fold (freeable_match_map_entry c r)
}
```

let freeable_match'_cases_pred
  (x: freeable_cbor')
  (ft: freeable_tree)
: GTot bool
  (decreases ft)
= match x, ft with
  | FBytes _, FTBytes
  | FBox _, FTBox _
  | FArray _, FTArray _
  | FMap _, FTMap _
  | FUnit, FTUnit
   -> true
  | _ -> false

```pulse
ghost
fn freeable_match'_cases
  (x: freeable_cbor')
  (ft: freeable_tree)
requires
  freeable_match' x ft
ensures
  freeable_match' x ft ** pure (freeable_match'_cases_pred x ft)
{
  let test = freeable_match'_cases_pred x ft;
  if test {
    ()
  } else {
    rewrite (freeable_match' x ft) as (pure False);
    rewrite emp as (freeable_match' x ft); //  by contradiction
  }
}
```

inline_for_extraction
let cbor_free'_t =
  (x: freeable_cbor') ->
  (ft: freeable_tree) ->
  stt unit
    (freeable_match' x ft)
    (fun _ -> emp)

inline_for_extraction
```pulse
fn cbor_free_map_entry
  (cbor_free': cbor_free'_t)
  (x: freeable_cbor_map_entry)
  (ft: Ghost.erased (freeable_tree & freeable_tree))
requires
    (freeable_match_map_entry x ft)
ensures
    (emp)
{
  unfold (freeable_match_map_entry x ft);
  cbor_free' x.map_entry_key _;
  cbor_free' x.map_entry_value _;
}
```

```pulse
fn rec cbor_free'
  (x: freeable_cbor')
  (ft: freeable_tree)
requires
  freeable_match' x ft
ensures
  emp
{
  freeable_match'_cases x ft;
  match x {
    FUnit -> {
      unfold (freeable_match' FUnit FTUnit);
    }
    FBytes v -> {
      unfold (freeable_match' (FBytes v) FTBytes);
      V.free v
    }
    FBox b -> {
      let ft' = Ghost.hide (FTBox?.b ft);
      unfold (freeable_match' (FBox b) (FTBox ft'));
      B.free b.box_cbor;
      let b' = ((let open Pulse.Lib.Box in ( ! )) b.box_footprint);
      cbor_free' b' _;
      B.free b.box_footprint
    }
    FArray a -> {
      let ft' = Ghost.hide (FTArray?.a ft);
      unfold (freeable_match' (FArray a) (FTArray ft'));
      V.free a.array_cbor;
      with s . assert (pts_to a.array_footprint s ** SM.seq_list_match s ft' freeable_match');
      V.pts_to_len a.array_footprint;
      SM.seq_list_match_length freeable_match' s ft';
      SM.seq_list_match_seq_seq_match freeable_match' s ft';
      let len = a.array_len;
      with s' . assert (SM.seq_seq_match freeable_match' s s' 0 (SZ.v len));
      let mut pi = 0sz;
      while (
        let i = !pi;
        (SZ.lt i len)
      ) invariant b . exists* i j . (
        pts_to a.array_footprint s **
        pts_to pi i **
        SM.seq_seq_match freeable_match' s s' j (SZ.v len) **
        pure (
          j == SZ.v i /\
          SZ.v i <= SZ.v len /\
          b == (SZ.v i < SZ.v len)
        )
      ) {
        SM.seq_seq_match_dequeue_left freeable_match' s s' _ _;
        let i = !pi;
        let x' = V.op_Array_Access a.array_footprint i;
        cbor_free' x' _;
        pi := (SZ.add i 1sz);
      };
      SM.seq_seq_match_empty_elim freeable_match' s s' (SZ.v len);
      V.free a.array_footprint
    }
    FMap a -> {
      let ft' = Ghost.hide (FTMap?.m ft);
      unfold (freeable_match' (FMap a) (FTMap ft'));
      V.free a.map_cbor;
      with s . assert (pts_to a.map_footprint s ** SM.seq_list_match s ft' (freeable_match_map_entry' ft freeable_match'));
      SM.seq_list_match_weaken s ft' (freeable_match_map_entry' ft freeable_match') freeable_match_map_entry (freeable_match_map_entry_weaken ft);
      V.pts_to_len a.map_footprint;
      SM.seq_list_match_length freeable_match_map_entry s ft';
      SM.seq_list_match_seq_seq_match freeable_match_map_entry s ft';
      let len = a.map_len;
      with s' . assert (SM.seq_seq_match freeable_match_map_entry s s' 0 (SZ.v len));
      let mut pi = 0sz;
      while (
        let i = !pi;
        (SZ.lt i len)
      ) invariant b . exists* i j . (
        pts_to a.map_footprint s **
        pts_to pi i **
        SM.seq_seq_match freeable_match_map_entry s s' j (SZ.v len) **
        pure (
          j == SZ.v i /\
          SZ.v i <= SZ.v len /\
          b == (SZ.v i < SZ.v len)
        )
      ) {
        SM.seq_seq_match_dequeue_left freeable_match_map_entry s s' _ _;
        let i = !pi;
        let x' = V.op_Array_Access a.map_footprint i;
        cbor_free_map_entry cbor_free' x' _;
        pi := (SZ.add i 1sz);
      };
      SM.seq_seq_match_empty_elim freeable_match_map_entry s s' (SZ.v len);
      V.free a.map_footprint
    }
  }
}
```

  
  
