module CDDL.Pulse.MapGroup
include CDDL.Spec.MapGroup.Base
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base

module R = Pulse.Lib.Reference
module U64 = FStar.UInt64

noeq
type linked_list_cell = {
  value: U64.t;
  tail: R.ref linked_list;
}

and linked_list = option linked_list_cell

let match_linked_list_cons_prop
  (l0: list (cbor & cbor))
  (c: linked_list_cell)
  (a: (cbor & cbor))
: Tot prop
=
        U64.v c.value < List.Tot.length l0 /\
        a == List.Tot.index l0 (U64.v c.value)

let match_linked_list_cons
  (l0: list (cbor & cbor))
  (c: linked_list_cell)
  (a: (cbor & cbor))
  (q: list (cbor & cbor))
  (match_linked_list: ((ll: linked_list) -> (l: list (cbor & cbor) { l << a :: q }) -> slprop))
: Tot slprop
=
    exists* ll' .
      R.pts_to c.tail ll' **
      match_linked_list ll' q **
      pure (match_linked_list_cons_prop l0 c a)

let rec match_linked_list
  (l0: list (cbor & cbor))
  (ll: linked_list)
  (l: list (cbor & cbor))
: Tot slprop
  (decreases l)
= match ll, l with
  | _, [] -> pure (None? ll)
  | Some c, a :: q -> match_linked_list_cons l0 c a q (match_linked_list l0)
  | _ -> pure False

let list_not_defined_at
  (#t: eqtype)
  (#t' : Type)
  (l: list (t & t'))
  (x: (t & t'))
: Tot bool
= None? (List.Tot.assoc (fst x) l)

type impl_map_group_result =
  | MGOK
  | MGFail
  | MGCutFail

let impl_map_group_for_excluded_post
  (res: impl_map_group_result)
  (g: map_group)
  (m: cbor_map)
  (vexcluded: list (cbor & cbor))
: Tot prop
=
  match res, apply_map_group_det g (cbor_map_filter (list_not_defined_at vexcluded) m) with
              | MGOK, MapGroupDet _ rem -> rem == cbor_map_empty
              | MGFail, MapGroupFail -> True
              | MGCutFail, MapGroupCutFail -> True
              | _ -> False

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_map_group_for_excluded
  (#cbor_map_iterator_t: Type)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
    (g: map_group)
    (i: cbor_map_iterator_t)
    (p: perm)
    (l: (list (cbor & cbor)))
    (m: cbor_map)
    (pexcluded: R.ref linked_list)
    (lexcluded: linked_list)
    (vexcluded: (list (cbor & cbor)))
= unit ->
    stt impl_map_group_result
        (
            cbor_map_iterator_match p i l **
            R.pts_to pexcluded lexcluded **
            match_linked_list l lexcluded vexcluded **
            pure (List.Tot.no_repeats_p (List.Tot.map fst l) /\
              (forall x . cbor_map_get m x == List.Tot.assoc x l) /\
              FStar.UInt.fits (List.Tot.length l) 64
            )
        )
        (fun res -> exists* lexcluded' .
            cbor_map_iterator_match p i l **
            R.pts_to pexcluded lexcluded' **
            match_linked_list l lexcluded vexcluded **
            pure (
              impl_map_group_for_excluded_post res g m vexcluded
            )
        )

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_map_group_for
  (#cbor_map_iterator_t: Type)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
    (g: map_group)
    (i: cbor_map_iterator_t)
    (p: perm)
    (l: (list (cbor & cbor)))
    (m: cbor_map)
=
    (pexcluded: R.ref linked_list) ->
    (#lexcluded: Ghost.erased linked_list) ->
    (#vexcluded: Ghost.erased (list (cbor & cbor))) ->
    impl_map_group_for_excluded cbor_map_iterator_match g i p l m pexcluded lexcluded vexcluded

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_map_group
  (#cbor_map_iterator_t: Type)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
    (g: map_group)
=
    (i: cbor_map_iterator_t) ->
    (#p: perm) ->
    (#l: Ghost.erased (list (cbor & cbor))) ->
    (m: Ghost.erased cbor_map) ->
    impl_map_group_for cbor_map_iterator_match g i p l m

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_map_group_cps
  (#cbor_map_iterator_t: Type)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
    (g: map_group)
=
    (i: cbor_map_iterator_t) ->
    (#p: perm) ->
    (#l: Ghost.erased (list (cbor & cbor))) ->
    (m: Ghost.erased cbor_map) ->
    (g': Ghost.erased map_group) ->
    (cont: impl_map_group_for cbor_map_iterator_match g' i p l m) ->
    impl_map_group_for cbor_map_iterator_match (map_group_concat g g') i p l m

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_group_concat
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#g1: Ghost.erased map_group)
  (ig1: impl_map_group_cps cbor_map_iterator_match g1)
  (#g2: Ghost.erased map_group)
  (ig2: impl_map_group cbor_map_iterator_match g2)
: impl_map_group u#0 #cbor_map_iterator_t cbor_map_iterator_match (map_group_concat g1 g2)
=
  (i: _)
  (#p: _)
  (#l: _)
  (m: _)
  (pexcluded: _)
  (#lexcluded: _)
  (#vexcluded: _)
  (_: unit)
{
  ig1 i #p #l m g2 (ig2 i #p #l m) pexcluded #lexcluded #vexcluded ()
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_t_map
  (#ty: Type0)
  (vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_map_iterator_init: map_iterator_start_t vmatch cbor_map_iterator_match)
  (#g: Ghost.erased map_group)
  (ig: impl_map_group cbor_map_iterator_match g)
: impl_typ u#0 #ty vmatch #None (t_map g)
=
  (c: _)
  (#p: _)
  (#v: _)
{
    let ty = cbor_get_major_type c;
    if (ty = cbor_major_type_map) {
      let m : Ghost.erased cbor_map = Ghost.hide (CMap?.c (unpack v));
      let i = cbor_map_iterator_init c;
      with pl l . assert (cbor_map_iterator_match pl i l);
      let lexcluded : linked_list = None #linked_list_cell;
      fold (match_linked_list l lexcluded []);
      let mut pexcluded = lexcluded;
      assert (pure (cbor_map_equal (cbor_map_filter (list_not_defined_at []) m) m));
      let res = ig i m pexcluded ();
      Trade.elim _ _;
      unfold (match_linked_list l lexcluded []);
      (res = MGOK)
    } else {
      false
    }
}
```
