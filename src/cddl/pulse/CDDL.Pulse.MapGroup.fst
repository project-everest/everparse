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
= match l with
  | [] -> pure (None? ll)
  | a :: q ->
    begin match ll with
    | Some c -> match_linked_list_cons l0 c a q (match_linked_list l0)
    | _ -> pure False
    end

```pulse
ghost
fn match_linked_list_is_nil
  (ll: linked_list)
  (#l0: (list (cbor & cbor)))
  (#l: (list (cbor & cbor)))
requires
  match_linked_list l0 ll l
ensures
  match_linked_list l0 ll l **
  pure (None? ll == Nil? l)
{
  match l {
    Nil -> {
      unfold (match_linked_list l0 ll []);
      fold (match_linked_list l0 ll []);
    }
    Cons a q -> {
      match ll {
        None -> {
          unfold (match_linked_list l0 None (a :: q));
          fold (match_linked_list l0 None (a :: q))
        }
        Some c -> { () }
      }
    }
  }
}
```

```pulse
ghost
fn match_linked_list_cons_elim
  (ll: linked_list)
  (c: linked_list_cell)
  (#l0: (list (cbor & cbor)))
  (#l: (list (cbor & cbor)))
requires
  match_linked_list l0 ll l **
  pure (Cons? l /\
    ll == Some c
  )
returns res: squash (Cons? l)
ensures exists* ll' .
  R.pts_to c.tail ll' **
  match_linked_list l0 ll' (List.Tot.tl l) **
  Trade.trade
    (R.pts_to c.tail ll' **
      match_linked_list l0 ll' (List.Tot.tl l))
    (match_linked_list l0 ll l) **
  pure (
    let i = U64.v (c.value) in
    i < List.Tot.length l0 /\
    List.Tot.index l0 i == List.Tot.hd l)
{
  match_linked_list_is_nil ll;
  let a = List.Tot.hd l;
  let q = List.Tot.tl l;
  unfold (match_linked_list l0 (Some c) (a :: q));
  unfold (match_linked_list_cons l0 c a q (match_linked_list l0));
  with ll' . assert (R.pts_to c.tail ll' ** match_linked_list l0 ll' q);
  ghost fn aux ()
    requires emp ** (R.pts_to c.tail ll' ** match_linked_list l0 ll' q)
    ensures match_linked_list l0 ll l
  {
    fold (match_linked_list_cons l0 c a q (match_linked_list l0));
    fold (match_linked_list l0 (Some c) (a :: q));
  };
  Trade.intro _ _ _ aux;
  ()
}
```

let rec list_index_map
  (#t1 #t2: Type)
  (f: (t1 -> t2))
  (l: list t1)
  (i: nat)
: Lemma
  (requires (i < List.Tot.length l))
  (ensures (
    let l' = List.Tot.map f l in
    i < List.Tot.length l' /\
    List.Tot.index l' i == f (List.Tot.index l i)
  ))
  [SMTPat (List.Tot.index (List.Tot.map f l) i)]
= if i = 0
  then ()
  else list_index_map f (List.Tot.tl l) (i - 1)

let rec list_no_repeats_index_inj'
  (#t: Type)
  (l: list t)
  (i1 i2: nat)
: Lemma
  (requires (i1 <= i2 /\ i2 < List.Tot.length l /\
    List.Tot.no_repeats_p l /\
    List.Tot.index l i1 == List.Tot.index l i2
  ))
  (ensures (
    i1 == i2
  ))
  (decreases l)
= if i1 = 0
  then ()
  else list_no_repeats_index_inj' (List.Tot.tl l) (i1 - 1) (i2 - 1)

let list_no_repeats_index_inj
  (#t: Type)
  (l: list t)
  (i1 i2: nat)
: Lemma
  (requires (i1 < List.Tot.length l /\
    i2 < List.Tot.length l /\
    List.Tot.no_repeats_p l    
  ))
  (ensures (
    (i1 == i2 <==> List.Tot.index l i1 == List.Tot.index l i2)
  ))
= if (i1 <= i2)
  then Classical.move_requires (list_no_repeats_index_inj' l i1) i2
  else Classical.move_requires (list_no_repeats_index_inj' l i2) i1

inline_for_extraction
```pulse
fn match_linked_list_mem
  (ll: linked_list)
  (x: U64.t)
  (#l0: Ghost.erased (list (cbor & cbor)))
  (#l: Ghost.erased (list (cbor & cbor)))
requires
  match_linked_list l0 ll l **
  pure (
    List.Tot.no_repeats_p (List.Tot.map fst l0) /\
    U64.v x < List.Tot.length l0
  )
returns res: bool
ensures
  match_linked_list l0 ll l **
  pure (U64.v x < List.Tot.length l0 /\
    res == Some? (List.Tot.assoc (fst (List.Tot.index l0 (U64.v x))) l)
  )
{
  let mut pll = ll;
  let mut pres = false;
  Trade.refl (match_linked_list l0 ll l);
  while (
    let res = !pres;
    if (res) {
      false
    } else {
      let ll1 = !pll;
      match_linked_list_is_nil ll1;
      Some? ll1
    }
  )
  invariant b . exists* ll1 l1 res .
    R.pts_to pll ll1 **
    match_linked_list l0 ll1 l1 **
    Trade.trade
      (match_linked_list l0 ll1 l1)
      (match_linked_list l0 ll l) **
    R.pts_to pres res **
    pure (
      Some? (List.Tot.assoc (fst (List.Tot.index l0 (U64.v x))) l) == (res || Some? (List.Tot.assoc (fst (List.Tot.index l0 (U64.v x))) l1)) /\
      b == (Cons? l1 && not res)
    )
  {
    let ll1 = !pll;
    match_linked_list_is_nil ll1;
    let c = Some?.v ll1;
    match_linked_list_cons_elim ll1 c;
    let i = c.value;
    list_no_repeats_index_inj (List.Tot.map fst l0) (U64.v x) (U64.v i);
    if (x = i) {
      Trade.elim _ (match_linked_list l0 ll1 _);
      pres := true;
    } else {
      Trade.trans _ _ (match_linked_list l0 ll l);
      let ll2 = ! c.tail;
      Trade.elim_hyp_l _ _ _;
      pll := ll2;
    }
  };
  Trade.elim _ _;
  !pres
}
```

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
              | MGCutFail, MapGroupCutFail -> True
              | _, MapGroupNonDet -> False
              | MGFail, MapGroupDet _ rem -> ~ (rem == cbor_map_empty)
              | MGFail, MapGroupFail -> True
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

module U = CBOR.Spec.Util

let cbor_map_filter_true_eq : squash (map_group_filter (U.truep) == map_group_nop)
= assert (forall f . cbor_map_filter (U.notp U.truep) f `cbor_map_equal` cbor_map_empty);
  apply_map_group_det_map_group_equiv (map_group_filter (U.truep)) map_group_nop

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_map_entry_cond
  (#t: Type)
  (vmatch2: perm -> t -> cbor & cbor -> slprop)
  (f: ((cbor & cbor) -> bool))
=
  (x: t) ->
  (#p: perm) ->
  (#v: Ghost.erased (cbor & cbor)) ->
  stt bool
    (vmatch2 p x v)
    (fun res -> vmatch2 p x v ** pure (res == f v))

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_entry_cond_true
  (#t: Type0)
  (vmatch2: perm -> t -> cbor & cbor -> slprop)
: impl_map_entry_cond u#0 #t vmatch2 U.truep
= (x: _)
  (#p: _)
  (#v: _)
{
  true
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_entry_cond_not
  (#t: Type0)
  (#vmatch2: perm -> t -> cbor & cbor -> slprop)
  (#f: Ghost.erased ((cbor & cbor) -> bool))
  (impf: impl_map_entry_cond vmatch2 f)
: impl_map_entry_cond u#0 #t vmatch2 (U.notp f)
= (x: _)
  (#p: _)
  (#v: _)
{
  let nres = impf x;
  not nres
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_entry_cond_and
  (#t: Type0)
  (#vmatch2: perm -> t -> cbor & cbor -> slprop)
  (#f1: Ghost.erased ((cbor & cbor) -> bool))
  (impf1: impl_map_entry_cond vmatch2 f1)
  (#f2: Ghost.erased ((cbor & cbor) -> bool))
  (impf2: impl_map_entry_cond vmatch2 f2)
: impl_map_entry_cond u#0 #t vmatch2 (U.andp f1 f2)
= (x: _)
  (#p: _)
  (#v: _)
{
  let res1 = impf1 x;
  if (res1) {
    impf2 x
  } else {
    false
  }
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_entry_cond_or
  (#t: Type0)
  (#vmatch2: perm -> t -> cbor & cbor -> slprop)
  (#f1: Ghost.erased ((cbor & cbor) -> bool))
  (impf1: impl_map_entry_cond vmatch2 f1)
  (#f2: Ghost.erased ((cbor & cbor) -> bool))
  (impf2: impl_map_entry_cond vmatch2 f2)
: impl_map_entry_cond u#0 #t vmatch2 (orp f1 f2)
= (x: _)
  (#p: _)
  (#v: _)
{
  let res1 = impf1 x;
  if (res1) {
    true
  } else {
    impf2 x
  }
}
```

let list_nil_forall_not_memP
  (#t: Type)
  (l: list t)
: Lemma
  (Nil? l <==> forall x . ~ (List.Tot.memP x l))
= ()

module GR = Pulse.Lib.GhostReference

let rec list_index_append_cons
  (#t: Type)
  (l1: list t)
  (x: t)
  (l2: list t)
: Lemma
  (ensures (let i = List.Tot.length l1 in
    let l = List.Tot.append l1 (x :: l2) in
    i < List.Tot.length l /\
    List.Tot.index l i == x
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_index_append_cons q x l2

let list_filter_cons_intro
  (#t: Type)
  (f: t -> bool)
  (a: t)
  (q: list t)
: Lemma
  (requires (f a))
  (ensures (Cons? (List.Tot.filter f (a :: q))))
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_group_filter
  (#t: Type0)
  (#vmatch2: perm -> t -> cbor & cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (cbor_map_iterator_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (cbor_map_iterator_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (#f: Ghost.erased ((cbor & cbor) -> bool))
  (implf: impl_map_entry_cond vmatch2 f)
: impl_map_group u#0 #cbor_map_iterator_t cbor_map_iterator_match (map_group_filter f)
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
  let mut pi = i;
  let mut pres = true;
  let pl1 : GR.ref (list (cbor & cbor)) = GR.alloc (Nil #(cbor & cbor));
  let mut pj = 0uL;
  let ll = !pexcluded;
  Trade.refl (cbor_map_iterator_match p i l);
  cbor_map_filter_filter f (list_not_defined_at vexcluded) m;
  list_nil_forall_not_memP (List.Tot.filter (U.andp (list_not_defined_at vexcluded) f) l);
  Classical.forall_intro_2 (U.list_assoc_no_repeats_mem l);
  assert (pure (
    cbor_map_filter f (cbor_map_filter (list_not_defined_at vexcluded) m) `cbor_map_equal'` cbor_map_empty <==> Nil? (List.Tot.filter (U.andp (list_not_defined_at vexcluded) f) l)
  ));
  while (
    let res = !pres;
    if (res) {
      with i2 l2 . assert (cbor_map_iterator_match p i2 l2);
      let j2 = !pi;
      Trade.rewrite_with_trade
        (cbor_map_iterator_match p i2 l2)
        (cbor_map_iterator_match p j2 l2);
      let is_emp = cbor_map_iterator_is_empty j2;
      Trade.elim _ (cbor_map_iterator_match p i2 l2);
      not is_emp
    } else {
      false
    }
  )
  invariant b. exists* i2 j l1 l2 res .
    R.pts_to pi i2 **
    cbor_map_iterator_match p i2 l2 **
    R.pts_to pj j **
    R.pts_to pres res **
    GR.pts_to pl1 l1 **
     Trade.trade
      (cbor_map_iterator_match p i2 l2)
      (cbor_map_iterator_match p i l) **
    match_linked_list l ll vexcluded **
    pure (
      l == List.Tot.append l1 l2 /\
      List.Tot.length l1 == U64.v j /\
      b == (res && Cons? l2) /\
      (cbor_map_filter f (cbor_map_filter (list_not_defined_at vexcluded) m) == cbor_map_empty <==> (res == true /\ Nil? (List.Tot.filter (U.andp (list_not_defined_at vexcluded) f) l2)))
    )
  {
    let j = !pj;
    with l1 . assert (GR.pts_to pl1 l1);
    with gi2 l2 . assert (cbor_map_iterator_match p gi2 l2);
    list_index_append_cons l1 (List.Tot.hd l2) (List.Tot.tl l2);
    let entry = cbor_map_iterator_next pi;
    Trade.trans _ _ (cbor_map_iterator_match p i l);
    let is_excluded = match_linked_list_mem ll j;
    pj := U64.add j 1uL;
    List.Tot.append_assoc l1 [List.Tot.hd l2] (List.Tot.tl l2);
    List.Tot.append_length l1 [List.Tot.hd l2];
    GR.op_Colon_Equals pl1 (List.Tot.append l1 [List.Tot.hd l2]);
    if (not is_excluded) {
      let matches = implf entry;
      Trade.elim_hyp_l _ _ _;
      pres := not matches;
    } else {
      Trade.elim_hyp_l _ _ _;
    }
  };
  Trade.elim _ _;
  GR.free pl1;
  let res = !pres;
  if (res) {
    MGOK
  } else {
    MGFail
  }
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_map_group_of_cps
  (#t: Type0)
  (#vmatch2: perm -> t -> cbor & cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (cbor_map_iterator_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (cbor_map_iterator_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (#g1: Ghost.erased map_group)
  (ig1: impl_map_group_cps cbor_map_iterator_match g1)
: impl_map_group u#0 #cbor_map_iterator_t cbor_map_iterator_match g1
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
  map_group_concat_nop_r g1;
  impl_map_group_concat ig1 (impl_map_group_filter cbor_map_iterator_is_empty cbor_map_iterator_next (impl_map_entry_cond_true _)) i #p #l m pexcluded #lexcluded #vexcluded ()
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
