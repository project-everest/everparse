module CBOR.Pulse.Raw.Copy
#lang-pulse
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open Pulse { pts_to }

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box

[@@erasable]
noeq
type freeable_tree = // this is necessary to define the freeable slprop by structural recursion, because cbor_freeable0 is not structurally recursive because V.vec and B.box may introduce cycles
| FTBytes
| FTBox: (b: freeable_tree) -> freeable_tree
| FTArray: (a: list freeable_tree) -> freeable_tree
| FTMap: (m: list (freeable_tree & freeable_tree)) -> freeable_tree
| FTUnit

noeq
type cbor_freeable0 =
| CBOR_Copy_Bytes: (v: V.vec U8.t) -> cbor_freeable0
| CBOR_Copy_Box: (b: cbor_freeable_box) -> cbor_freeable0
| CBOR_Copy_Array: (a: cbor_freeable_array) -> cbor_freeable0
| CBOR_Copy_Map: (m: cbor_freeable_map) -> cbor_freeable0
| CBOR_Copy_Unit

and cbor_freeable_box = {
  box_cbor: B.box cbor_raw; // the box turned into ref in cbor_tagged
  box_footprint: B.box cbor_freeable0; // the cbor_freeable associated to the contents of box_cbor
}

and cbor_freeable_array = {
  array_cbor: V.vec cbor_raw; // the vec turned into slice in cbor_array
  array_footprint: V.vec cbor_freeable0; // the cbor_freeable objects associated to each element of array_cbor
  array_len: (array_len: SZ.t { SZ.v array_len == V.length array_footprint });
}

and cbor_freeable_map_entry = {
  map_entry_key: cbor_freeable0;
  map_entry_value: cbor_freeable0;
}

and cbor_freeable_map = {
  map_cbor: V.vec cbor_map_entry; // the vec turned into slice in cbor_map
  map_footprint: V.vec cbor_freeable_map_entry; // the cbor_freeable objects associated to each map entry key and value of map_cbor
  map_len: (map_len: SZ.t { SZ.v map_len == V.length map_footprint });
}

module SM = Pulse.Lib.SeqMatch.Util

let rec freeable_match'
  (x: cbor_freeable0)
  (ft: freeable_tree)
: Tot slprop
  (decreases ft)
= match x, ft with
  | CBOR_Copy_Bytes ve, FTBytes -> exists* (v: Seq.seq U8.t) . pts_to ve v ** pure (V.is_full_vec ve)
  | CBOR_Copy_Box bx, FTBox ft' -> exists* (v: cbor_raw) (x': cbor_freeable0) . pts_to bx.box_cbor v ** pts_to bx.box_footprint x' ** freeable_match' x' ft'
  | CBOR_Copy_Array ar, FTArray ft' -> exists* (v: Seq.seq cbor_raw) (x': Seq.seq cbor_freeable0) . pts_to ar.array_cbor v ** pts_to ar.array_footprint x' ** SM.seq_list_match x' ft' freeable_match' ** pure (V.is_full_vec ar.array_cbor /\ V.is_full_vec ar.array_footprint)
  | CBOR_Copy_Map m, FTMap ft' -> exists* (v: Seq.seq cbor_map_entry) (x': Seq.seq cbor_freeable_map_entry) . pts_to m.map_cbor v ** pts_to m.map_footprint x' ** SM.seq_list_match x' ft' (freeable_match_map_entry' ft freeable_match') ** pure (V.is_full_vec m.map_cbor /\ V.is_full_vec m.map_footprint)
  | CBOR_Copy_Unit, FTUnit -> emp
  | _ -> pure False
    
and freeable_match_map_entry'
  (r0: freeable_tree)
  (freeable_match: (cbor_freeable0 -> (v': freeable_tree { v' << r0 }) -> slprop))
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
: Tot slprop
  (decreases r)
= freeable_match' c.map_entry_key (fst r) **
  freeable_match' c.map_entry_value (snd r)

let freeable_match_box
  (bx: cbor_freeable_box)
  (ft': freeable_tree)
: Tot slprop
= exists* (v: cbor_raw) (x': cbor_freeable0) . pts_to bx.box_cbor v ** pts_to bx.box_footprint x' ** freeable_match' x' ft'

let freeable_match_box_eq
  (bx: cbor_freeable_box)
  (ft': freeable_tree)
: Lemma
  (freeable_match' (CBOR_Copy_Box bx) (FTBox ft') == freeable_match_box bx ft')
= assert_norm (freeable_match' (CBOR_Copy_Box bx) (FTBox ft') == freeable_match_box bx ft')

let freeable_match_map_entry
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree))
: Tot slprop
  (decreases r)
= freeable_match' c.map_entry_key (fst r) **
  freeable_match' c.map_entry_value (snd r)

ghost
fn freeable_match_map_entry_weaken
  (r0: freeable_tree)
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_map_entry' r0 freeable_match' c r
ensures
  freeable_match_map_entry c r
{
  unfold (freeable_match_map_entry' r0 freeable_match' c r);
  fold (freeable_match_map_entry c r)
}

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

ghost
fn freeable_match_map_entry_weaken_recip
  (r0: list (freeable_tree & freeable_tree))
  (c: cbor_freeable_map_entry)
  (r: (freeable_tree & freeable_tree) { r << r0 })
requires
  freeable_match_map_entry c r
ensures
  freeable_match_map_entry' (FTMap r0) freeable_match' c r
{
  unfold (freeable_match_map_entry c r);
  fold (freeable_match_map_entry' (FTMap r0) freeable_match' c r);
}

let freeable_match'_cases_pred
  (x: cbor_freeable0)
  (ft: freeable_tree)
: GTot bool
  (decreases ft)
= match x, ft with
  | CBOR_Copy_Bytes _, FTBytes
  | CBOR_Copy_Box _, FTBox _
  | CBOR_Copy_Array _, FTArray _
  | CBOR_Copy_Map _, FTMap _
  | CBOR_Copy_Unit, FTUnit
   -> true
  | _ -> false

ghost
fn freeable_match'_cases
  (x: cbor_freeable0)
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

inline_for_extraction
let cbor_free'_t =
  (x: cbor_freeable0) ->
  (ft: freeable_tree) ->
  stt unit
    (freeable_match' x ft)
    (fun _ -> emp)

inline_for_extraction
fn cbor_free_map_entry
  (cbor_free': cbor_free'_t)
  (x: cbor_freeable_map_entry)
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

fn rec cbor_free'
  (x: cbor_freeable0)
  (ft: freeable_tree)
requires
  freeable_match' x ft
ensures
  emp
{
  freeable_match'_cases x ft;
  match x {
    CBOR_Copy_Unit -> {
      unfold (freeable_match' CBOR_Copy_Unit FTUnit);
    }
    CBOR_Copy_Bytes v -> {
      unfold (freeable_match' (CBOR_Copy_Bytes v) FTBytes);
      V.free v
    }
    CBOR_Copy_Box b -> {
      let ft' = Ghost.hide (FTBox?.b ft);
      unfold (freeable_match' (CBOR_Copy_Box b) (FTBox ft'));
      B.free b.box_cbor;
      let b' = ((let open Pulse.Lib.Box in ( ! )) b.box_footprint);
      cbor_free' b' _;
      B.free b.box_footprint
    }
    CBOR_Copy_Array a -> {
      let ft' = Ghost.hide (FTArray?.a ft);
      unfold (freeable_match' (CBOR_Copy_Array a) (FTArray ft'));
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
          SZ.v i <= SZ.v len
        ) ** pure (
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
    CBOR_Copy_Map a -> {
      let ft' = Ghost.hide (FTMap?.m ft);
      unfold (freeable_match' (CBOR_Copy_Map a) (FTMap ft'));
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
          SZ.v i <= SZ.v len
        ) ** pure (
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

noeq
type cbor_freeable = {
  cbor: cbor_raw;
  footprint: cbor_freeable0;
  tree: freeable_tree;
}

let freeable (f: cbor_freeable) : Tot slprop = freeable_match' f.footprint f.tree

fn rec cbor_free0
  (x: cbor_freeable)
requires
  freeable x
ensures
  emp
{
  unfold (freeable x);
  cbor_free' x.footprint _
}

open CBOR.Pulse.Raw.Read
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let cbor_copy_t =
  (x: cbor_raw) ->
  (#p: perm) ->
  (#v: Ghost.erased raw_data_item) ->
  stt cbor_freeable
    (cbor_match p x v)
    (fun res ->
      cbor_match p x v **
      cbor_match 1.0R res.cbor v **
      Trade.trade
        (cbor_match 1.0R res.cbor v)
        (freeable res)
    )

inline_for_extraction
fn cbor_copy_map_entry
  (copy: cbor_copy_t)
  (x: cbor_map_entry)
  (#p: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires
    (cbor_match_map_entry p x v)
returns res: (cbor_freeable & cbor_freeable)
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

module S = Pulse.Lib.Slice

inline_for_extraction
let get_cbor_raw_array
  (x: cbor_raw { CBOR_Case_Array? x })
: Tot cbor_array
= let CBOR_Case_Array v = x in v

inline_for_extraction
fn rec cbor_copy_array
  (copy: cbor_copy_t)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match p x v ** pure (CBOR_Case_Array? x))
returns res: cbor_freeable
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
  let a = get_cbor_raw_array x;
  cbor_match_eq_array p a v;
  Trade.rewrite_with_trade
    (cbor_match p x v)
    (cbor_match_array a p v cbor_match);
  cbor_match_array_elim a p v;
  Trade.trans _ _ (cbor_match p x v);
  let ar = a.cbor_array_ptr;
  rewrite each a.cbor_array_ptr as ar;
  S.pts_to_len ar;
  with ps s pl l . assert (pts_to ar #ps s ** SM.seq_list_match s l (cbor_match pl));
  SM.seq_list_match_length (cbor_match pl) s l;
  let len = S.len ar;
  let v' = V.alloc (CBOR_Case_Simple 0uy (* dummy *)) len;
  V.pts_to_len v';
  let vf = V.alloc CBOR_Copy_Unit (* dummy *) len;
  V.pts_to_len vf;
  with s0 . assert (pts_to v' s0);
  with sf0 . assert (pts_to vf sf0);
  let sl = Ghost.hide (Seq.seq_of_list l);
  SM.seq_seq_match_empty_intro (cbor_match 1.0R) s0 sl 0;
  intro
    (Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s0 sl 0 0)
      (SM.seq_seq_match freeable_match' sf0 (Seq.create (SZ.v len) FTUnit (* dummy *)) 0 0)
    )
    #emp
    fn _
  {
    SM.seq_seq_match_empty_elim (cbor_match 1.0R) s0 sl 0;
    SM.seq_seq_match_empty_intro freeable_match' sf0 (Seq.create (SZ.v len) FTUnit (* dummy *)) 0;
  };
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i len)
  ) invariant b . exists* i s1 j sf st . (
    pts_to ar #ps s ** SM.seq_list_match s l (cbor_match pl) **
    pts_to pi i **
    pts_to v' s1 **
    SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j **
    pts_to vf sf **
    Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match' sf st 0 j) **
    pure (
      j == SZ.v i /\
      j <= SZ.v len /\
      Seq.length st == SZ.v len
    ) ** pure (
      b == (j < SZ.v len)
    )
  ) {
    S.pts_to_len ar;
    V.pts_to_len v';
    V.pts_to_len vf;
    let i = !pi;
    with s1 sf st . assert (pts_to v' s1 ** pts_to vf sf ** Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 (SZ.v i))
      (SM.seq_seq_match freeable_match' sf st 0 (SZ.v i))
    );
    let c = ar.(i);
    SM.seq_list_match_index_trade (cbor_match pl) s l (SZ.v i);
    let c' = copy c;
    rewrite each Seq.index s (SZ.v i) as c;
    Trade.elim _ (SM.seq_list_match s l (cbor_match pl));
    with v1 . assert (cbor_match 1.0R c'.cbor v1 ** Trade.trade (cbor_match 1.0R c'.cbor v1) (freeable c'));
    V.op_Array_Assignment v' i c'.cbor;
    with s1' . assert (pts_to v' s1');
    V.op_Array_Assignment vf i c'.footprint;
    with sf' . assert (pts_to vf sf');
    SM.seq_seq_match_rewrite_seq_trade (cbor_match 1.0R) s1 s1' sl sl 0 (SZ.v i);
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i)) _ _;
    Trade.prod (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i)) _ (cbor_match 1.0R c'.cbor v1) _;
    SM.seq_seq_match_enqueue_right_trade (cbor_match 1.0R) s1' sl 0 (SZ.v i) c'.cbor v1;
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    let st' = Ghost.hide (Seq.upd st (SZ.v i) c'.tree);
    intro
      (Trade.trade
        (SM.seq_seq_match freeable_match' sf st 0 (SZ.v i) ** freeable c')
        (SM.seq_seq_match freeable_match' sf' st' 0 (SZ.v i + 1))
      )
      #emp
      fn _
    {
      SM.seq_seq_match_rewrite_seq freeable_match' sf sf' st st' 0 (SZ.v i);
      unfold (freeable c');
      SM.seq_seq_match_enqueue_right freeable_match' sf' st' 0 (SZ.v i) c'.footprint c'.tree;
    };
    Trade.trans (SM.seq_seq_match (cbor_match 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    pi := (SZ.add i 1sz);
  };
  Trade.elim _ (cbor_match p x v);
  with s1 sf st . assert (pts_to v' s1 ** pts_to vf sf ** 
    SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 (SZ.v len) **
    Trade.trade
      (SM.seq_seq_match (cbor_match 1.0R) s1 sl 0 (SZ.v len))
      (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
  );
  V.pts_to_len v';
  SM.seq_seq_match_seq_list_match_trade (cbor_match 1.0R) s1 sl;
  Trade.trans _ _ (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len));
  V.pts_to_len vf;
  let lt = Ghost.hide (Seq.seq_to_list st);
  intro
    (Trade.trade
      (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
      (SM.seq_list_match sf lt freeable_match')
    )
    #emp
    fn _
  {
    rewrite (SM.seq_seq_match freeable_match' sf st 0 (SZ.v len))
      as (SM.seq_seq_match freeable_match' sf (Seq.seq_of_list lt) 0 (SZ.v len));
    SM.seq_seq_match_seq_list_match freeable_match' sf lt;
  };
  Trade.trans _ _ (SM.seq_list_match sf lt freeable_match');
  V.to_array_pts_to v';
  let ar' = S.from_array (V.vec_to_array v') len;
  S.pts_to_len ar';
  let c' = cbor_match_array_intro len64 ar';
  Trade.trans_concl_r _ _ _ _;
  let fa = {
    array_cbor = v';
    array_footprint = vf;
    array_len = len;
  };
  let res = {
    cbor = c';
    footprint = CBOR_Copy_Array fa;
    tree = FTArray lt;
  };
  intro
    (Trade.trade
      (pts_to ar' s1 ** SM.seq_list_match sf lt freeable_match')
      (freeable res)
    )
    #(S.is_from_array (V.vec_to_array v') ar' ** pts_to vf sf)
    fn _
  {
   S.to_array ar';
   V.to_vec_pts_to v';
   rewrite (pts_to v' s1) as (pts_to fa.array_cbor s1);
   rewrite (pts_to vf sf) as (pts_to fa.array_footprint sf);
   fold (freeable_match' (CBOR_Copy_Array fa) (FTArray lt));
   fold (freeable res)
  };
  Trade.trans _ _ (freeable res);
  res
}

inline_for_extraction
let get_cbor_raw_map
  (x: cbor_raw { CBOR_Case_Map? x })
: Tot cbor_map
= let CBOR_Case_Map v = x in v

#restart-solver

inline_for_extraction
fn rec cbor_copy_map
  (copy: cbor_copy_t)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match p x v ** pure (CBOR_Case_Map? x))
returns res: cbor_freeable
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
  let a = get_cbor_raw_map x;
  cbor_match_eq_map0 p a v;
  Trade.rewrite_with_trade
    (cbor_match p x v)
    (cbor_match_map0 a p v cbor_match);
  cbor_match_map0_map_trade a p v;
  Trade.trans _ _ (cbor_match p x v);
  cbor_match_map_elim a p v;
  Trade.trans _ _ (cbor_match p x v);
  let ar = a.cbor_map_ptr;
  rewrite each a.cbor_map_ptr as ar;
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
  let vf = V.alloc
    ({
      map_entry_key = CBOR_Copy_Unit;
      map_entry_value = CBOR_Copy_Unit;
    })
    len;
  V.pts_to_len vf;
  with s0 . assert (pts_to v' s0);
  with sf0 . assert (pts_to vf sf0);
  let sl = Ghost.hide (Seq.seq_of_list l);
  SM.seq_seq_match_empty_intro (cbor_match_map_entry 1.0R) s0 sl 0;
  intro
    (Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s0 sl 0 0)
      (SM.seq_seq_match freeable_match_map_entry sf0 (Seq.create (SZ.v len) (FTUnit, FTUnit) (* dummy *)) 0 0)
    )
    #emp
    fn _
  {
    SM.seq_seq_match_empty_elim (cbor_match_map_entry 1.0R) s0 sl 0;
    SM.seq_seq_match_empty_intro freeable_match_map_entry sf0 (Seq.create (SZ.v len) (FTUnit, FTUnit) (* dummy *)) 0;
  };
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i len)
  ) invariant b . exists* i s1 j sf st . (
    pts_to ar #ps s ** SM.seq_list_match s l (cbor_match_map_entry pl) **
    pts_to pi i **
    pts_to v' s1 **
    SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j **
    pts_to vf sf **
    Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 j)
      (SM.seq_seq_match freeable_match_map_entry sf st 0 j) **
    pure (
      j == SZ.v i /\
      j <= SZ.v len /\
      Seq.length st == SZ.v len
    ) ** pure (
      b == (j < SZ.v len)
    )
  ) {
    S.pts_to_len ar;
    V.pts_to_len v';
    V.pts_to_len vf;
    let i = !pi;
    with s1 sf st . assert (pts_to v' s1 ** pts_to vf sf ** Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 (SZ.v i))
      (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v i))
    );
    let c = S.op_Array_Access ar i;
    SM.seq_list_match_index_trade (cbor_match_map_entry pl) s l (SZ.v i);
    with v1 . assert (cbor_match_map_entry pl c v1);
    let key', value' = cbor_copy_map_entry copy c;
    Trade.elim _ (SM.seq_list_match s l (cbor_match_map_entry pl));
    Trade.prod
      (cbor_match 1.0R key'.cbor (fst v1))
      (freeable key')
      (cbor_match 1.0R value'.cbor (snd v1))
      (freeable value');
    let cme' = {
      cbor_map_entry_key = key'.cbor;
      cbor_map_entry_value = value'.cbor;
    };
    Trade.rewrite_with_trade
      (cbor_match 1.0R key'.cbor (fst v1) **
        cbor_match 1.0R value'.cbor (snd v1)
      )
      (cbor_match_map_entry 1.0R cme' v1);
    Trade.trans (cbor_match_map_entry 1.0R cme' v1) _ _;
    V.op_Array_Assignment v' i cme';
    with s1' . assert (pts_to v' s1');
    let cfp' = {
      map_entry_key = key'.footprint;
      map_entry_value = value'.footprint;
    };
    V.op_Array_Assignment vf i cfp';
    with sf' . assert (pts_to vf sf');
    SM.seq_seq_match_rewrite_seq_trade (cbor_match_map_entry 1.0R) s1 s1' sl sl 0 (SZ.v i);
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i)) _ _;
    Trade.prod (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i)) _ (cbor_match_map_entry 1.0R cme' v1) _;
    SM.seq_seq_match_enqueue_right_trade (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i) cme' v1;
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    let tree = Ghost.hide (key'.tree, value'.tree);
    let st' = Ghost.hide (Seq.upd st (SZ.v i) tree);
    intro
      (Trade.trade
        (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v i) ** (freeable key' ** freeable value'))
        (SM.seq_seq_match freeable_match_map_entry sf' st' 0 (SZ.v i + 1))
      )
      #emp
      fn _
    {
      SM.seq_seq_match_rewrite_seq freeable_match_map_entry sf sf' st st' 0 (SZ.v i);
      unfold (freeable key');
      unfold (freeable value');
      rewrite each key'.footprint as cfp'.map_entry_key;
      rewrite each value'.footprint as cfp'.map_entry_value;
      fold (freeable_match_map_entry cfp' (key'.tree, value'.tree));
      SM.seq_seq_match_enqueue_right freeable_match_map_entry sf' st' 0 (SZ.v i) cfp' (key'.tree, value'.tree);
    };
    Trade.trans (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1' sl 0 (SZ.v i + 1)) _ _;
    pi := (SZ.add i 1sz);
  };
  Trade.elim _ (cbor_match p x v);
  with s1 sf st . assert (pts_to v' s1 ** pts_to vf sf ** 
    SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 (SZ.v len) **
    Trade.trade
      (SM.seq_seq_match (cbor_match_map_entry 1.0R) s1 sl 0 (SZ.v len))
      (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
  );
  V.pts_to_len v';
  SM.seq_seq_match_seq_list_match_trade (cbor_match_map_entry 1.0R) s1 sl;
  Trade.trans _ _ (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len));
  V.pts_to_len vf;
  let lt = Ghost.hide (Seq.seq_to_list st);
  intro
    (Trade.trade
      (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
      (SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'))
    )
    #emp
    fn _
  {
    rewrite (SM.seq_seq_match freeable_match_map_entry sf st 0 (SZ.v len))
      as (SM.seq_seq_match freeable_match_map_entry sf (Seq.seq_of_list lt) 0 (SZ.v len));
    SM.seq_seq_match_seq_list_match freeable_match_map_entry sf lt;
    SM.seq_list_match_weaken sf lt freeable_match_map_entry (freeable_match_map_entry' (FTMap lt) freeable_match') (freeable_match_map_entry_weaken_recip lt);
  };
  Trade.trans _ _ (SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'));
  V.to_array_pts_to v';
  let ar' = S.from_array (V.vec_to_array v') len;
  S.pts_to_len ar';
  let c' = cbor_match_map_intro len64 ar';
  Trade.trans_concl_r _ _ _ _;
  let fa = {
    map_cbor = v';
    map_footprint = vf;
    map_len = len;
  };
  let res = {
    cbor = c';
    footprint = CBOR_Copy_Map fa;
    tree = FTMap lt;
  };
  intro
    (Trade.trade
      (pts_to ar' s1 ** SM.seq_list_match sf lt (freeable_match_map_entry' (FTMap lt) freeable_match'))
      (freeable res)
    )
    #(S.is_from_array (V.vec_to_array v') ar' ** pts_to vf sf)
    fn _
  {
   S.to_array ar';
   V.to_vec_pts_to v';
   rewrite (pts_to v' s1) as (pts_to fa.map_cbor s1);
   rewrite (pts_to vf sf) as (pts_to fa.map_footprint sf);
   fold (freeable_match' (CBOR_Copy_Map fa) (FTMap lt));
   fold (freeable res)
  };
  Trade.trans _ _ (freeable res);
  res
}

fn rec cbor_copy0
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
    (cbor_match p x v)
returns res: cbor_freeable
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
        footprint = CBOR_Copy_Unit;
        tree = FTUnit;
      };
      intro
        (Trade.trade
          (cbor_match 1.0R c' (Int64 ty w))
          (freeable res)
        )
        #emp
        fn _
      {
        cbor_match_int_free c';
        fold (freeable_match' CBOR_Copy_Unit FTUnit);
        fold (freeable res)
      };
      res
    }
    CBOR_Case_Simple _ -> {
      let w = cbor_match_simple_elim x;
      let c' = cbor_match_simple_intro w;
      let res = {
        cbor = c';
        footprint = CBOR_Copy_Unit;
        tree = FTUnit;
      };
      intro
        (Trade.trade
          (cbor_match 1.0R c' (Simple w))
          (freeable res)
        )
        #emp
        fn _
      {
        cbor_match_simple_free c';
        fold (freeable_match' CBOR_Copy_Unit FTUnit);
        fold (freeable res)
      };
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
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      intro
        (Trade.trade
          (pts_to s' vs')
          (freeable res)
        )
        #(S.is_from_array (V.vec_to_array v') s')
        fn _
      {
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        fold (freeable res)
      };
      Trade.trans _ (pts_to s' vs') _;
      res
    }
    CBOR_Case_Tagged _ -> {
      let tag = cbor_match_tagged_get_tag x;
      let pl = cbor_match_tagged_get_payload x;
      let cpl' = cbor_copy0 pl;
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
        footprint = CBOR_Copy_Box fb;
        tree = FTBox cpl'.tree
      };
      intro
        (Trade.trade
          (pts_to (B.box_to_ref b) cpl'.cbor ** freeable cpl')
          (freeable res)
        )
        #(pts_to bf cpl'.footprint)
        fn _
      {
        B.to_box_pts_to b;
        rewrite (pts_to bf cpl'.footprint) as (pts_to fb.box_footprint cpl'.footprint);
        rewrite (pts_to b cpl'.cbor) as (pts_to fb.box_cbor) (cpl'.cbor);
        unfold (freeable cpl');
        fold (freeable_match_box fb cpl'.tree);
        freeable_match_box_eq fb cpl'.tree;
        rewrite (freeable_match_box fb cpl'.tree) as (freeable_match' (CBOR_Copy_Box fb) (FTBox cpl'.tree));
        fold (freeable res)
      };
      Trade.trans _ _ (freeable res);
      res
    }
    CBOR_Case_Array a -> {
      cbor_copy_array cbor_copy0 (CBOR_Case_Array a);
    }
    CBOR_Case_Map a -> {
      cbor_copy_map cbor_copy0 (CBOR_Case_Map a);
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
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      Trade.intro_trade
        (cbor_match_serialized_array a' 1.0R v)
        (freeable res)
        (
          Trade.trade
            (cbor_match_serialized_payload_array s' 1.0R (Array?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        )
        fn _
      {
        unfold (cbor_match_serialized_array a' 1.0R v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        fold (freeable res)
      };
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
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      Trade.intro_trade
        (cbor_match_serialized_map a' 1.0R v)
        (freeable res)
        (
          Trade.trade
            (cbor_match_serialized_payload_map s' 1.0R (Map?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        )
        fn _
      {
        unfold (cbor_match_serialized_map a' 1.0R v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        fold (freeable res)
      };
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
        footprint = CBOR_Copy_Bytes v';
        tree = FTBytes;
      };
      Trade.intro_trade
        (cbor_match_serialized_tagged a' 1.0R v)
        (freeable res)
        (
          Trade.trade
            (cbor_match_serialized_payload_tagged s' 1.0R (Tagged?.v v))
            (exists* v_ . pts_to s' v_) **
          S.is_from_array (V.vec_to_array v') s'
        )
        fn _
      {
        unfold (cbor_match_serialized_tagged a' 1.0R v);
        Trade.elim _ _;
        S.to_array s';
        V.to_vec_pts_to v';
        fold (freeable_match' (CBOR_Copy_Bytes v') FTBytes);
        fold (freeable res)
      };
      Trade.rewrite_with_trade
        (cbor_match_serialized_tagged a' 1.0R v)
        (cbor_match 1.0R res.cbor v);
      Trade.trans (cbor_match 1.0R res.cbor v) _ _;
      res
    }
  }
}
