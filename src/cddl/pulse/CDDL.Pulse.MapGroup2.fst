module CDDL.Pulse.MapGroup2
include CDDL.Spec.MapGroup
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base

module R = Pulse.Lib.Reference
module U64 = FStar.UInt64

type impl_map_group_result =
  | MGOK
  | MGFail
  | MGCutFail

unfold
let impl_map_group_pre
  (g: map_group)
  (f: typ)
  (v: cbor)
  (m1 m2: cbor_map)
  (i: U64.t)
: Tot prop
= map_group_footprint g f /\
  cbor_map_disjoint m1 m2 /\
  cbor_map_disjoint_from_footprint m2 f /\
  cbor_map_length m1 == U64.v i /\
  begin match unpack v with
  | CMap m ->
    cbor_map_equal m (cbor_map_union m1 m2)
  | _ -> False
  end

let impl_map_group_post
  (g: map_group)
  (f: typ)
  (v: cbor)
  (m1 m2: cbor_map)
  (i: U64.t)
  (i': U64.t)
  (res: impl_map_group_result)
: Tot prop
= impl_map_group_pre g f v m1 m2 i /\
  begin match apply_map_group_det g m1, res with
  | MapGroupDet consumed remaining, MGOK ->
    cbor_map_length remaining == U64.v i'
  | MapGroupFail, MGFail -> True
  | MapGroupCutFail, MGCutFail -> True
  | _ -> False
  end

inline_for_extraction
let impl_map_group_t
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (g: map_group)
  (f: typ)
=
  (c: t) ->
  (#p: perm) ->
  (#v: Ghost.erased cbor) ->
  (v1: Ghost.erased cbor_map) ->
  (v2: Ghost.erased cbor_map) ->
  (pi: R.ref U64.t) ->
  (#i: Ghost.erased U64.t) ->
  stt impl_map_group_result
        (
          vmatch p c v **
          pts_to pi i **
          pure (impl_map_group_pre g f v v1 v2 i)
        )
        (fun res -> exists* i' .
          vmatch p c v **
          pts_to pi i' **
          pure (impl_map_group_post g f v v1 v2 i i' res)
        )

inline_for_extraction
```pulse
fn apply_impl_map_group
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g: Ghost.erased map_group)
  (#f: Ghost.erased typ)
  (w: impl_map_group_t vmatch g f)
  (c: t)
  (#p: perm)
  (#v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
  (pi: R.ref U64.t)
  (#i: Ghost.erased U64.t)
  (sq: squash (
    impl_map_group_pre g f v v1 v2 i
  ))
requires
        (
          vmatch p c v **
          pts_to pi i
        )
returns res: impl_map_group_result
ensures
        (exists* i' .
          vmatch p c v **
          pts_to pi i' **
          pure (impl_map_group_post g f v v1 v2 i i' res)
        )
{
  w c v1 v2 pi
}
```

inline_for_extraction
```pulse
fn impl_t_map_group
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (get_map_length: get_map_length_t vmatch)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased typ)
  (w1: impl_map_group_t vmatch g1 f1)
  (sq: squash (map_group_footprint g1 f1))
: impl_typ u#0 #_ vmatch #None (t_map g1)
= (c: _)
  (#p: _)
  (#v: _)
{
  let ty = cbor_get_major_type c;
  if (ty = cbor_major_type_map) {
    let m = Ghost.hide (CMap?.c (unpack v) <: cbor_map); // coercion needed because of the refinement on CMap?.c
    let rem0 : U64.t = get_map_length c;
    let mut remaining = rem0;
    let res : impl_map_group_result = w1 c m cbor_map_empty remaining;
    match res {
      MGOK -> {
        let rem = !remaining;
        Classical.forall_intro cbor_map_length_empty_equiv;
        (rem = 0uL)
      }
      MGFail -> {
        false
      }
      MGCutFail -> {
        false
      }
    }
  } else {
    false
  }
}
```

inline_for_extraction
```pulse
fn impl_map_group_nop
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (_: unit)
: impl_map_group_t #_ vmatch (map_group_nop) (t_always_false)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (pi: _)
  (#i: _)
{
  MGOK
}
```

inline_for_extraction
```pulse
fn impl_map_group_always_false
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (_: unit)
: impl_map_group_t #_ vmatch (map_group_always_false) (t_always_false)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (pi: _)
  (#i: _)
{
  MGFail
}
```

inline_for_extraction
```pulse
fn impl_map_group_concat
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased typ)
  (w1: impl_map_group_t vmatch g1 f1)
  (#g2: Ghost.erased map_group)
  (#f2: Ghost.erased typ)
  (w2: impl_map_group_t vmatch g2 f2)
  (prf: squash (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2
  ))
: impl_map_group_t #_ vmatch (map_group_concat g1 g2) (t_choice f1 f2)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (pi: _)
  (#i: _)
{
  let res1 = w1 c v1 v2 pi;
  match res1 {
    MGOK -> {
      let m = Ghost.hide (CMap?.c (unpack v));
      let vres = Ghost.hide (apply_map_group_det g1 v1);
      let vconsumed = Ghost.hide (MapGroupDet?.consumed vres);
      let vremaining = Ghost.hide (MapGroupDet?.remaining vres);
      let v2' = Ghost.hide (cbor_map_union vconsumed v2);
      map_group_footprint_consumed_disjoint g1 f1 f2 v1;
      let res = w2 c vremaining v2' pi;
      res
    }
    MGFail -> {
      MGFail
    }
    MGCutFail -> {
      MGCutFail
    }
  }
}
```

inline_for_extraction
```pulse
fn impl_map_group_choice
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased typ)
  (w1: impl_map_group_t vmatch g1 f1)
  (#g2: Ghost.erased map_group)
  (#f2: Ghost.erased typ)
  (w2: impl_map_group_t vmatch g2 f2)
  (prf: squash (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
: impl_map_group_t #_ vmatch (map_group_choice g1 g2) (t_choice f1 f2)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (pi: _)
  (#i: _)
{
  let i0 = !pi;
  let res1 = w1 c v1 v2 pi;
  match res1 {
    MGOK -> {
      MGOK
    }
    MGFail -> {
      pi := i0;
      let res = w2 c v1 v2 pi;
      res
    }
    MGCutFail -> {
      MGCutFail
    }
  }
}
```

let impl_map_group_match_item_for_body_post
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (cut: bool)
  (k: Ghost.erased cbor)
  (dest: Ghost.erased typ)
  (c: t)
  (p: perm)
  (v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
  (pi: R.ref U64.t)
  (i: Ghost.erased U64.t)
  (res: impl_map_group_result)
= exists* i' .
          vmatch p c v **
          pts_to pi i' **
          pure (impl_map_group_post (map_group_match_item_for cut k dest) (t_literal k) v v1 v2 i i' res)

inline_for_extraction
```pulse
fn impl_map_group_match_item_for_body
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (map_get: map_get_t vmatch)
  (cut: bool)
  (k: Ghost.erased cbor)
  (dest: Ghost.erased typ)
  (vdest: impl_typ vmatch dest)
  (c: t)
  (p: perm)
  (v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
  (pi: R.ref U64.t)
  (i: Ghost.erased U64.t)
: with_cbor_literal_cont_t #_ vmatch k
          (vmatch p c v ** pts_to pi i **
            pure (impl_map_group_pre (map_group_match_item_for cut k dest) (t_literal k) v v1 v2 i)
          )
  impl_map_group_result
  (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 pi i)
= (pk: _)
  (ck: _)
{
  let mg = map_get c ck;
  match mg {
    None -> {
      unfold (map_get_post vmatch c p v k None);
      unfold (map_get_post_none vmatch c p v k);
      fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 pi i MGFail);
      MGFail
    }
    Some cv -> {
      unfold (map_get_post vmatch c p v k (Some cv));
      unfold (map_get_post_some vmatch c p v k cv);
      with pv vv . assert (vmatch pv cv vv);
      let check_value = vdest cv;
      Trade.elim _ _;
      if (check_value) {
        let i1 = !pi;
        cbor_map_length_empty_equiv v1;
        let i2 = U64.sub i1 1uL;
        pi := i2;
        let rm' = Ghost.hide (MapGroupDet?.remaining (apply_map_group_det (map_group_match_item_for cut k dest) v1));
        cbor_map_length_disjoint_union (cbor_map_singleton k vv) rm';
        fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 pi i MGOK);
        MGOK
      } else if cut {
        fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 pi i MGCutFail);
        MGCutFail
      } else {
        fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 pi i MGFail);
        MGFail
      }
    }
  }
}
```

inline_for_extraction
```pulse
fn impl_map_group_match_item_for
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (map_get: map_get_t vmatch)
  (cut: bool)
  (#k: Ghost.erased cbor)
  (wk: with_cbor_literal_t vmatch k)
  (#dest: Ghost.erased typ)
  (vdest: impl_typ vmatch dest)
: impl_map_group_t #_ vmatch (map_group_match_item_for cut k dest) (t_literal k)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (pi: _)
  (#i: _)
{
  let res = wk _ _ _ (impl_map_group_match_item_for_body map_get cut k dest vdest c p v v1 v2 pi i);
  unfold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 pi i);
  res
}
```
