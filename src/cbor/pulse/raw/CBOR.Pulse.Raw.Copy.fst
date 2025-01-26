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

module SM = Pulse.Lib.SeqMatch.Util

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

let freeable_match_box
  (bx: freeable_cbor_box)
  (ft': freeable_tree)
: Tot slprop
= exists* (v: cbor_raw) (x': freeable_cbor') . pts_to bx.box_cbor v ** pts_to bx.box_footprint x' ** freeable_match' x' ft'

let freeable_match_box_eq
  (bx: freeable_cbor_box)
  (ft': freeable_tree)
: Lemma
  (freeable_match' (FBox bx) (FTBox ft') == freeable_match_box bx ft')
= assert_norm (freeable_match' (FBox bx) (FTBox ft') == freeable_match_box bx ft')

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

let ftmap_precedes'
  (r: freeable_tree { FTMap? r })
: Lemma
  (FTMap?.m r << r)
= ()

let ftmap_precedes
  (r0: list (freeable_tree & freeable_tree))
: Lemma
  (ensures (r0 << FTMap r0))
  [SMTPat (FTMap r0)]
= ftmap_precedes' (FTMap r0)

```pulse
ghost
fn freeable_match_map_entry_weaken_recip
  (r0: list (freeable_tree & freeable_tree))
  (c: freeable_cbor_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_map_entry c r
ensures
  freeable_match_map_entry' (FTMap r0) freeable_match' c r
{
  unfold (freeable_match_map_entry c r);
  fold (freeable_match_map_entry' (FTMap r0) freeable_match' c r);
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

noeq
type freeable_cbor = {
  cbor: cbor_raw;
  footprint: freeable_cbor';
  tree: freeable_tree;
}

let freeable (f: freeable_cbor) : Tot slprop = freeable_match' f.footprint f.tree

```pulse
fn rec cbor_free
  (x: freeable_cbor)
requires
  freeable x
ensures
  emp
{
  unfold (freeable x);
  cbor_free' x.footprint _
}
```

open CBOR.Pulse.Raw.Read
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let cbor_copy_t =
  (x: cbor_raw) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item) ->
  stt freeable_cbor
    (cbor_match p x v)
    (fun res ->
      cbor_match p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )

inline_for_extraction
```pulse
fn cbor_copy_map_entry
  (copy: cbor_copy_t)
  (x: cbor_map_entry)
  (#p: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires
    (cbor_match_map_entry p x v)
returns res: (freeable_cbor & freeable_cbor)
ensures
    (
      cbor_match_map_entry p x v **
      cbor_match 1.0R (fst res).cbor (fst v) **
      cbor_match 1.0R (snd res).cbor (snd v) **
      Trade.trade
        (cbor_match 1.0R (fst res).cbor (fst v))
        (freeable (fst res)) **
      Trade.trade
        (cbor_match 1.0R (snd res).cbor (snd v))
        (freeable (snd res))
    )
{
  unfold (cbor_match_map_entry p x v);
  let key = copy x.cbor_map_entry_key;
  let value = copy x.cbor_map_entry_value;
  fold (cbor_match_map_entry p x v);
  (key, value)
}
```

module S = Pulse.Lib.Slice

inline_for_extraction
```pulse
fn rec cbor_copy_array
  (copy: cbor_copy_t)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match p x v ** pure (CBOR_Case_Array? x))
returns res: freeable_cbor
ensures
    (
      cbor_match p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_cases x;
  let len64 = cbor_match_array_get_length x;
  let a = CBOR_Case_Array?.v x;
  cbor_match_eq_array p a v;
  Trade.rewrite_with_trade
    (cbor_match p x v)
    (cbor_match_array a p v cbor_match);
  cbor_match_array_elim a p v;
  Trade.trans _ _ (cbor_match p x v);
  let ar = a.cbor_array_ptr;
  S.pts_to_len ar;
  with ps s pl l . assert (pts_to ar #ps s ** SM.seq_list_match s l (cbor_match pl));
  SM.seq_list_match_length (cbor_match pl) s l;
  let len = S.len ar;
  let v' = V.alloc (CBOR_Case_Simple 0uy (* dummy *)) len;
  V.pts_to_len v';
  V.to_array_pts_to v';
  let ar' = S.from_array (V.vec_to_array v') len;
  S.pts_to_len ar';
  let vf = V.alloc FUnit (* dummy *) len;
  V.pts_to_len vf;
  with s0 . assert (pts_to ar' s0);
  with sf0 . assert (pts_to vf sf0);
  let sl = Ghost.hide (Seq.seq_of_list l);
  SM.seq_seq_match_empty_intro (cbor_match 1.0R) s0 sl 0;
  ghost fn aux0 (_: unit)
  requires emp ** SM.seq_seq_match (cbor_match 1.0R) s0 sl 0 0
  ensures SM.seq_seq_match freeable_match' sf0 (Seq.create (SZ.v len) FTUnit (* dummy *)) 0 0
  {
    SM.seq_seq_match_empty_elim (cbor_match 1.0R) s0 sl 0;
    SM.seq_seq_match_empty_intro freeable_match' sf0 (Seq.create (SZ.v len) FTUnit (* dummy *)) 0;
  };
  Trade.intro _ _ _ aux0;
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i len)
  ) invariant b . exists* i s1 j sf st . (
    pts_to ar #ps s ** SM.seq_list_match s l (cbor_match pl) **
    pts_to pi i **
    pts_to ar' s1 **
    SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j **
    pts_to vf sf **
    Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match' sf st 0 j) **
    pure (
      j == SZ.v i /\
      j <= SZ.v len /\
      b == (j < SZ.v len) /\
      Seq.length st == SZ.v len
    )
  ) {
    S.pts_to_len ar;
    S.pts_to_len ar';
    V.pts_to_len vf;
    let i = !pi;
    with s1 sf st . assert (pts_to ar' s1 ** pts_to vf sf ** Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 (SZ.v i))
      (SM.seq_seq_match freeable_match' sf st 0 (SZ.v i))
    );
    let c = S.op_Array_Access ar i;
    SM.seq_list_match_index_trade (cbor_match pl) s l (SZ.v i);
    let c' = copy c;
    Trade.elim _ (SM.seq_list_match s l (cbor_match pl));
    with v1 . assert (cbor_match 1.0R c'.cbor v1 ** Trade.trade (cbor_match 1.0R c'.cbor v1) (freeable c'));
    S.op_Array_Assignment ar' i c'.cbor;
    with s1' . assert (pts_to ar' s1');
    V.op_Array_Assignment vf i c'.footprint;
    with sf' . assert (pts_to vf sf');
    SM.seq_seq_match_rewrite_seq_trade (cbor_match 1.0R) s1 s1' sl sl 0 (SZ.v i);
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i)) _ _;
    Trade.prod (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i)) _ (cbor_match 1.0R c'.cbor v1) _;
    SM.seq_seq_match_enqueue_right_trade (cbor_match 1.0R) s1' sl 0 (SZ.v i) c'.cbor v1;
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    let st' = Ghost.hide (Seq.upd st (SZ.v i) c'.tree);
    ghost fn aux (_: unit)
    requires emp ** (SM.seq_seq_match freeable_match' sf st 0 (SZ.v i) ** freeable c')
    ensures SM.seq_seq_match freeable_match' sf' st' 0 (SZ.v i + 1)
    {
      SM.seq_seq_match_rewrite_seq freeable_match' sf sf' st st' 0 (SZ.v i);
      unfold (freeable c');
      SM.seq_seq_match_enqueue_right freeable_match' sf' st' 0 (SZ.v i) c'.footprint c'.tree;
    };
    Trade.intro _ _ _ aux;
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    pi := (SZ.add i 1sz);
  };
  Trade.elim _ (cbor_match p x v);
  with s1 sf st . assert (pts_to ar' s1 ** pts_to vf sf ** 
    SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 (SZ.v len) **
    Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 (SZ.v len))
      (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
  );
  S.pts_to_len ar';
  SM.seq_seq_match_seq_list_match_trade (cbor_match 1.0R) s1 sl;
  Trade.trans _ _ (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len));
  V.pts_to_len vf;
  let lt = Ghost.hide (Seq.seq_to_list st);
  ghost fn auxf (_: unit)
  requires
    emp ** SM.seq_seq_match freeable_match' sf st 0 (SZ.v len)
  ensures SM.seq_list_match sf lt freeable_match'
  {
    rewrite (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
      as (SM.seq_seq_match freeable_match' sf (Seq.seq_of_list lt) 0 (SZ.v len));
    SM.seq_seq_match_seq_list_match freeable_match' sf lt;
  };
  Trade.intro _ _ _ auxf;
  Trade.trans _ _ (SM.seq_list_match sf lt freeable_match');
  let c' = cbor_match_array_intro len64 ar';
  Trade.trans_concl_r _ _ _ _;
  let fa = {
    array_cbor = v';
    array_footprint = vf;
    array_len = len;
  };
  let res = {
    cbor = c';
    footprint = FArray fa;
    tree = FTArray lt;
  };
  ghost fn aux_res (_: unit)
  requires
    (S.is_from_array (V.vec_to_array v') ar' ** pts_to vf sf) **
    (pts_to ar' s1 ** SM.seq_list_match sf lt freeable_match')
  ensures
    freeable res
  {
   S.to_array ar';
   V.to_vec_pts_to v';
   rewrite (pts_to v' s1) as (pts_to fa.array_cbor s1);
   rewrite (pts_to vf sf) as (pts_to fa.array_footprint sf);
   fold (freeable_match' (FArray fa) (FTArray lt));
   fold (freeable res)
  };
  Trade.intro _ _ _ aux_res;
  Trade.trans _ _ (freeable res);
  res
}
```

#restart-solver

inline_for_extraction
```pulse
fn rec cbor_copy_map
  (copy: cbor_copy_t)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match p x v ** pure (CBOR_Case_Map? x))
returns res: freeable_cbor
ensures
    (
      cbor_match p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_cases x;
  let len64 = cbor_match_map_get_length x;
  let a = CBOR_Case_Map?.v x;
  cbor_match_eq_map0 p a v;
  Trade.rewrite_with_trade
    (cbor_match p x v)
    (cbor_match_map0 a p v cbor_match);
  cbor_match_map0_map_trade a p v;
  Trade.trans _ _ (cbor_match p x v);
  cbor_match_map_elim a p v;
  Trade.trans _ _ (cbor_match p x v);
  let ar = a.cbor_map_ptr;
  S.pts_to_len ar;
  with ps s pl l . assert (pts_to ar #ps s ** SM.seq_list_match s l (cbor_match_map_entry pl));
  SM.seq_list_match_length (cbor_match_map_entry pl) s l;
  let len = S.len ar;
  let v' = V.alloc
    ({
      cbor_map_entry_key = CBOR_Case_Simple 0uy; (* dummy *)
      cbor_map_entry_value = CBOR_Case_Simple 0uy;
    })
    len;
  V.pts_to_len v';
  V.to_array_pts_to v';
  let ar' = S.from_array (V.vec_to_array v') len;
  S.pts_to_len ar';
  let vf = V.alloc
    ({
      map_entry_key = FUnit;
      map_entry_value = FUnit;
    })
    len;
  V.pts_to_len vf;
  with s0 . assert (pts_to ar' s0);
  with sf0 . assert (pts_to vf sf0);
  let sl = Ghost.hide (Seq.seq_of_list l);
  SM.seq_seq_match_empty_intro (cbor_match_map_entry 1.0R) s0 sl 0;
  ghost fn aux0 (_: unit)
  requires emp ** SM.seq_seq_match (cbor_match_map_entry 1.0R) s0 sl 0 0
  ensures SM.seq_seq_match freeable_match_map_entry sf0 (Seq.create (SZ.v len) (FTUnit, FTUnit) (* dummy *)) 0 0
  {
    SM.seq_seq_match_empty_elim (cbor_match_map_entry 1.0R) s0 sl 0;
    SM.seq_seq_match_empty_intro freeable_match_map_entry sf0 (Seq.create (SZ.v len) (FTUnit, FTUnit) (* dummy *)) 0;
  };
  Trade.intro _ _ _ aux0;
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i len)
  ) invariant b . exists* i s1 j sf st . (
    pts_to ar #ps s ** SM.seq_list_match s l (cbor_match_map_entry pl) **
    pts_to pi i **
    pts_to ar' s1 **
    SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j **
    pts_to vf sf **
    Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match_map_entry sf st 0 j) **
    pure (
      j == SZ.v i /\
      j <= SZ.v len /\
      b == (j < SZ.v len) /\
      Seq.length st == SZ.v len
    )
  ) {
    S.pts_to_len ar;
    S.pts_to_len ar';
    V.pts_to_len vf;
    let i = !pi;
    with s1 sf st . assert (pts_to ar' s1 ** pts_to vf sf ** Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 (SZ.v i))
      (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v i))
    );
    let c = S.op_Array_Access ar i;
    SM.seq_list_match_index_trade (cbor_match_map_entry pl) s l (SZ.v i);
    with v1 . assert (cbor_match_map_entry pl c v1);
    let c' = cbor_copy_map_entry copy c;
    Trade.elim _ (SM.seq_list_match s l (cbor_match_map_entry pl));
    Trade.prod
      (cbor_match 1.0R (fst c').cbor (fst v1))
      (freeable (fst c'))
      (cbor_match 1.0R (snd c').cbor (snd v1))
      (freeable (snd c'));
    let cme' = {
      cbor_map_entry_key = (fst c').cbor;
      cbor_map_entry_value = (snd c').cbor;
    };
    Trade.rewrite_with_trade
      (cbor_match 1.0R (fst c').cbor (fst v1) **
        cbor_match 1.0R (snd c').cbor (snd v1)
      )
      (cbor_match_map_entry 1.0R cme' v1);
    Trade.trans (cbor_match_map_entry 1.0R cme' v1) _ _;
    S.op_Array_Assignment ar' i cme';
    with s1' . assert (pts_to ar' s1');
    let cfp' = {
      map_entry_key = (fst c').footprint;
      map_entry_value = (snd c').footprint;
    };
    V.op_Array_Assignment vf i cfp';
    with sf' . assert (pts_to vf sf');
    SM.seq_seq_match_rewrite_seq_trade (cbor_match_map_entry 1.0R) s1 s1' sl sl 0 (SZ.v i);
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i)) _ _;
    Trade.prod (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i)) _ (cbor_match_map_entry 1.0R cme' v1) _;
    SM.seq_seq_match_enqueue_right_trade (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i) cme' v1;
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    let tree = Ghost.hide ((fst c').tree, (snd c').tree);
    let st' = Ghost.hide (Seq.upd st (SZ.v i) tree);
    ghost fn aux (_: unit)
    requires emp ** (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v i) ** (freeable (fst c') ** freeable (snd c')))
    ensures SM.seq_seq_match freeable_match_map_entry sf' st' 0 (SZ.v i + 1)
    {
      SM.seq_seq_match_rewrite_seq freeable_match_map_entry sf sf' st st' 0 (SZ.v i);
      unfold (freeable (fst c'));
      unfold (freeable (snd c'));
      fold (freeable_match_map_entry cfp' tree);
      SM.seq_seq_match_enqueue_right freeable_match_map_entry sf' st' 0 (SZ.v i) cfp' tree;
    };
    Trade.intro _ _ _ aux;
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    pi := (SZ.add i 1sz);
  };
  Trade.elim _ (cbor_match p x v);
  with s1 sf st . assert (pts_to ar' s1 ** pts_to vf sf ** 
    SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 (SZ.v len) **
    Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 (SZ.v len))
      (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
  );
  S.pts_to_len ar';
  SM.seq_seq_match_seq_list_match_trade (cbor_match_map_entry 1.0R) s1 sl;
  Trade.trans _ _ (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len));
  V.pts_to_len vf;
  let lt = Ghost.hide (Seq.seq_to_list st);
  ghost fn auxf (_: unit)
  requires
    emp ** SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len)
  ensures SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match')
  {
    rewrite (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
      as (SM.seq_seq_match freeable_match_map_entry sf (Seq.seq_of_list lt) 0 (SZ.v len));
    SM.seq_seq_match_seq_list_match freeable_match_map_entry sf lt;
    SM.seq_list_match_weaken sf lt freeable_match_map_entry (freeable_match_map_entry' (FTMap lt) freeable_match') (freeable_match_map_entry_weaken_recip lt);
  };
  Trade.intro _ _ _ auxf;
  Trade.trans _ _ (SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'));
  let c' = cbor_match_map_intro len64 ar';
  Trade.trans_concl_r _ _ _ _;
  let fa = {
    map_cbor = v';
    map_footprint = vf;
    map_len = len;
  };
  let res = {
    cbor = c';
    footprint = FMap fa;
    tree = FTMap lt;
  };
  ghost fn aux_res (_: unit)
  requires
    (S.is_from_array (V.vec_to_array v') ar' ** pts_to vf sf) **
    (pts_to ar' s1 ** SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'))
  ensures
    freeable res
  {
   S.to_array ar';
   V.to_vec_pts_to v';
   rewrite (pts_to v' s1) as (pts_to fa.map_cbor s1);
   rewrite (pts_to vf sf) as (pts_to fa.map_footprint sf);
   fold (freeable_match' (FMap fa) (FTMap lt));
   fold (freeable res)
  };
  Trade.intro _ _ _ aux_res;
  Trade.trans _ _ (freeable res);
  res
}
```

```pulse
fn rec cbor_copy
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match p x v)
returns res: freeable_cbor
ensures
    (
      cbor_match p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )
{
  cbor_match_cases x;
  match x {
    CBOR_Case_Int _ -> {
      let ty = cbor_match_int_elim_type x;
      let w = cbor_match_int_elim_value x;
      let c' = cbor_match_int_intro ty w;
      let res = {
        cbor = c';
        footprint = FUnit;
        tree = FTUnit;
      };
      ghost fn aux (_: unit)
      requires emp ** cbor_match 1.0R c' (Int64 ty w)
      ensures freeable res
      {
        cbor_match_int_free c';
        fold (freeable_match' FUnit FTUnit);
        fold (freeable res)
      };
      Trade.intro_trade _ _ _ aux;
      res
    }
    CBOR_Case_Simple _ -> {
      let w = cbor_match_simple_elim x;
      let c' = cbor_match_simple_intro w;
      let res = {
        cbor = c';
        footprint = FUnit;
        tree = FTUnit;
      };
      ghost fn aux (_: unit)
      requires emp ** cbor_match 1.0R c' (Simple w)
      ensures freeable res
      {
        cbor_match_simple_free c';
        fold (freeable_match' FUnit FTUnit);
        fold (freeable res)
      };
      Trade.intro_trade _ _ _ aux;
      res
    }
    CBOR_Case_String _ -> {
      let ty = cbor_match_string_elim_type x;
      let len = cbor_match_string_elim_length x;
      let pl = cbor_match_string_elim_payload x;
      S.pts_to_len pl;
      let len_sz = S.len pl;
      let v' = V.alloc 0uy len_sz;
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len_sz;
      S.pts_to_len s';
      S.copy s' pl;
      Trade.elim _ _;
      with vs' . assert (pts_to s' vs');
      let c' = cbor_match_string_intro ty len s';
      let res = {
        cbor = c';
        footprint = FBytes v';
        tree = FTBytes;
      };
      ghost fn aux (_: unit)
      requires S.is_from_array (V.vec_to_array v') s' ** pts_to s' vs'
      ensures freeable res
      {
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (FBytes v') FTBytes);
        fold (freeable res)
      };
      Trade.intro _ _ _ aux;
      Trade.trans _ (pts_to s' vs') _;
      res
    }
    CBOR_Case_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag x;
      let pl = cbor_match_tagged_get_payload x;
      let cpl' = cbor_copy pl;
      Trade.elim _ (cbor_match p x v);
      let bf = B.alloc cpl'.footprint;
      let b = B.alloc cpl'.cbor;
      B.to_ref_pts_to b;
      let c' = cbor_match_tagged_intro tag (B.box_to_ref b);
      Trade.trans_concl_r _ _ _ _;
      let fb = {
          box_cbor = b;
          box_footprint = bf;
      };
      let res = {
        cbor = c';
        footprint = FBox fb;
        tree = FTBox cpl'.tree
      };
      ghost fn aux (_: unit)
      requires
        (pts_to bf cpl'.footprint ** (pts_to (B.box_to_ref b) cpl'.cbor ** freeable cpl'))
      ensures
        (freeable res)
      {
        B.to_box_pts_to b;
        rewrite (pts_to bf cpl'.footprint) as (pts_to fb.box_footprint cpl'.footprint);
        rewrite (pts_to b cpl'.cbor) as (pts_to fb.box_cbor) (cpl'.cbor);
        unfold (freeable cpl');
        fold (freeable_match_box fb cpl'.tree);
        freeable_match_box_eq fb cpl'.tree;
        rewrite (freeable_match_box fb cpl'.tree) as (freeable_match' (FBox fb) (FTBox cpl'.tree));
        fold (freeable res)
      };
      Trade.intro _ _ _ aux;
      Trade.trans _ _ (freeable res);
      res
    }
    CBOR_Case_Array a -> {
      cbor_copy_array cbor_copy (CBOR_Case_Array a);
    }
    CBOR_Case_Map a -> {
      cbor_copy_map cbor_copy (CBOR_Case_Map a);
    }
    CBOR_Case_Serialized_Array a -> {
      Trade.rewrite_with_trade
        (cbor_match p x v)
        (cbor_match_serialized_array a p v);
      unfold (cbor_match_serialized_array a p v);
      let len = S.len a.cbor_serialized_payload;
      let v' = V.alloc 0uy len;
      V.pts_to_len v';
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len;
      S.pts_to_len s';
      cbor_match_serialized_payload_array_copy a.cbor_serialized_payload _ _ s';
      fold (cbor_match_serialized_array a p v);
      Trade.elim _ (cbor_match p x v);
      let a' = {
        cbor_serialized_header = a.cbor_serialized_header;
        cbor_serialized_payload = s';
        cbor_serialized_perm = 1.0R;
      };
      fold (cbor_match_serialized_array a' 1.0R v);
      let res = {
        cbor = CBOR_Case_Serialized_Array a';
        footprint = FBytes v';
        tree = FTBytes;
      };
      ghost fn aux (_: unit)
      requires
        (
          Trade.trade
            (cbor_match_serialized_payload_array s' 1.0R (Array?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        ) ** cbor_match_serialized_array a' 1.0R v
      ensures freeable res
      {
        unfold (cbor_match_serialized_array a' 1.0R v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (FBytes v') FTBytes);
        fold (freeable res)
      };
      Trade.intro _ _ _ aux;
      Trade.rewrite_with_trade
        (cbor_match_serialized_array a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      res
    }
    CBOR_Case_Serialized_Map a -> {
      Trade.rewrite_with_trade
        (cbor_match p x v)
        (cbor_match_serialized_map a p v);
      unfold (cbor_match_serialized_map a p v);
      let len = S.len a.cbor_serialized_payload;
      let v' = V.alloc 0uy len;
      V.pts_to_len v';
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len;
      S.pts_to_len s';
      cbor_match_serialized_payload_map_copy a.cbor_serialized_payload _ _ s';
      fold (cbor_match_serialized_map a p v);
      Trade.elim _ (cbor_match p x v);
      let a' = {
        cbor_serialized_header = a.cbor_serialized_header;
        cbor_serialized_payload = s';
        cbor_serialized_perm = 1.0R;
      };
      fold (cbor_match_serialized_map a' 1.0R v);
      let res = {
        cbor = CBOR_Case_Serialized_Map a';
        footprint = FBytes v';
        tree = FTBytes;
      };
      ghost fn aux (_: unit)
      requires
        (
          Trade.trade
            (cbor_match_serialized_payload_map s' 1.0R (Map?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        ) ** cbor_match_serialized_map a' 1.0R v
      ensures freeable res
      {
        unfold (cbor_match_serialized_map a' 1.0R v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (FBytes v') FTBytes);
        fold (freeable res)
      };
      Trade.intro _ _ _ aux;
      Trade.rewrite_with_trade
        (cbor_match_serialized_map a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      res
    }
    CBOR_Case_Serialized_Tagged a -> {
      Trade.rewrite_with_trade
        (cbor_match p x v)
        (cbor_match_serialized_tagged a p v);
      unfold (cbor_match_serialized_tagged a p v);
      let len = S.len a.cbor_serialized_payload;
      let v' = V.alloc 0uy len;
      V.pts_to_len v';
      V.to_array_pts_to v';
      let s' = S.from_array (V.vec_to_array v') len;
      S.pts_to_len s';
      cbor_match_serialized_payload_tagged_copy a.cbor_serialized_payload _ _ s';
      fold (cbor_match_serialized_tagged a p v);
      Trade.elim _ (cbor_match p x v);
      let a' = {
        cbor_serialized_header = a.cbor_serialized_header;
        cbor_serialized_payload = s';
        cbor_serialized_perm = 1.0R;
      };
      fold (cbor_match_serialized_tagged a' 1.0R v);
      let res = {
        cbor = CBOR_Case_Serialized_Tagged a';
        footprint = FBytes v';
        tree = FTBytes;
      };
      ghost fn aux (_: unit)
      requires
        (
          Trade.trade
            (cbor_match_serialized_payload_tagged s' 1.0R (Tagged?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        ) ** cbor_match_serialized_tagged a' 1.0R v
      ensures freeable res
      {
        unfold (cbor_match_serialized_tagged a' 1.0R v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (FBytes v') FTBytes);
        fold (freeable res)
      };
      Trade.intro _ _ _ aux;
      Trade.rewrite_with_trade
        (cbor_match_serialized_tagged a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      res
    }
  }
}
```
