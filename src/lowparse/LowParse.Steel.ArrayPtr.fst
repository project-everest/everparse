module LowParse.Steel.ArrayPtr

module A = Steel.C.Array
module R = Steel.Reference

let g_is_null_from
  (#base #t0: Type0)
  (from: A.array_or_null_from base t0)
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (from == A.null_from base t0)

inline_for_extraction
noextract
let array'
  (#base #t0: Type0)
  (from: A.array_or_null_from base t0)
: Tot Type0
= (a: A.array base t0 { fst a == from })

(* I could define t as follows:
<<
noeq
type t
  (base: Type0)
  (t0: Type0)
= {
  from: A.array_or_null_from base t0;
  to: Ghost.erased (if g_is_null_from from then unit else R.ghost_ref (array' from));
}
>>

However, this dependent type does not extract to KReMLin very well (it is not inlined, etc.) Thus, instead, just like arrays, I can define t as a pair of an informative part and a ghost part, and move almost all dependency to the Ghost part, and express the remaining dependency between the informative part and the ghost part as a refinement:
*)

[@@erasable]
noeq
type t_nonnull
  (base: Type0)
  (t0: Type0)
= {
  from: A.array_or_null_from base t0;
  to: R.ghost_ref (array' from);
}

inline_for_extraction
noextract
let fst0 (#a #b: Type) (x: (a & b)) : Tot a = fst x
inline_for_extraction
noextract
let snd0 (#a #b: Type) (x: (a & b)) : Tot b = snd x

let t_prop
  (#base #t0: Type0)
  (x: (A.array_or_null_from base t0 & Ghost.erased (option (t_nonnull base t0))))
: Tot prop
= g_is_null_from (fst0 x) == None? (snd0 x) /\
  (Some? (snd0 x) ==> (Some?.v (snd0 x)).from == fst0 x)

let t base t0 =
  (x: (A.array_or_null_from base t0 & Ghost.erased (option (t_nonnull base t0))) { t_prop x })

let null base t0 = (A.null_from base t0, Ghost.hide None)

let g_is_null x =
  g_is_null_from (fst0 x)

let array base t = A.array base t

let len x = A.len x

let varrayptr0_refine
  (#base #a: Type)
  (x: t base a)
  (_: t_of emp)
: Tot prop
= g_is_null x == false

[@@__steel_reduce__]
let varrayptr0_dep_inner
  (#base #a: Type)
  (x: t base a)
  (_: t_of (emp `vrefine` varrayptr0_refine x))
  (ar: normal (t_of (R.ghost_vptr (Some?.v (snd0 x)).to)))
: Tot vprop
= A.varray ar

[@@__steel_reduce__]
let varrayptr0_dep_outer
  (#base #a: Type)
  (x: t base a)
  (q: t_of (emp `vrefine` varrayptr0_refine x))
: Tot vprop
= R.ghost_vptr (Some?.v (snd0 x)).to `vdep` varrayptr0_dep_inner x q

let varrayptr0_rewrite
  (#base #a: Type)
  (x: t base a)
  (res: normal (t_of (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_dep_outer x)))
: Tot (v base a)
= let (| _, (| ar, co |) |) = res in
  { array = ar; contents = co; }

[@@__steel_reduce__]
let varrayptr0
  (#base #a: Type)
  (x: t base a)
: Tot vprop
= emp `vrefine` varrayptr0_refine x
    `vdep` varrayptr0_dep_outer x
    `vrewrite` varrayptr0_rewrite x

val intro_varrayptr0
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
  (ar: A.array base a)
  (sq: squash (g_is_null x == false))
: SteelGhost unit opened
    (R.ghost_vptr (Some?.v (snd0 x)).to `star` A.varray ar)
    (fun _ -> varrayptr0 x)
    (requires (fun h ->
      h (R.ghost_vptr (Some?.v (snd0 x)).to) == ar
    ))
    (ensures (fun h _ h' ->
      let res = h' (varrayptr0 x) in
      res.array == ar /\
      res.contents == h (A.varray ar)
    ))

let intro_varrayptr0
  x ar sq
=
  intro_vrefine emp (varrayptr0_refine x);
  let q = gget (emp `vrefine` varrayptr0_refine x) in
  intro_vdep
    (R.ghost_vptr (Some?.v (snd0 x)).to)
    (A.varray ar)
    (varrayptr0_dep_inner x q);
  intro_vdep
    (emp `vrefine` varrayptr0_refine x)
    (R.ghost_vptr (Some?.v (snd0 x)).to `vdep` varrayptr0_dep_inner x q)
    (varrayptr0_dep_outer x);
  intro_vrewrite
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_dep_outer x)
    (varrayptr0_rewrite x)

val elim_varrayptr0
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost (Ghost.erased (R.ghost_ref (array' (fst0 x)) & A.array base a)) opened
    (varrayptr0 x)
    (fun res -> R.ghost_vptr (fst0 res) `star` A.varray (snd0 res))
    (requires (fun _ -> True))
    (ensures (fun h res h' ->
      let pres = h (varrayptr0 x) in
      let ar = snd0 res in
      g_is_null x == false /\
      fst0 res == (Some?.v (snd0 x)).to /\
      pres.array == Ghost.reveal ar /\
      h' (R.ghost_vptr (fst0 res)) == Ghost.reveal ar /\
      h' (A.varray ar) == pres.contents
    ))

let elim_varrayptr0 x =
  elim_vrewrite
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_dep_outer x)
    (varrayptr0_rewrite x);
  let q = elim_vdep (emp `vrefine` varrayptr0_refine x) (varrayptr0_dep_outer x) in
  elim_vrefine emp (varrayptr0_refine x);
  change_equal_slprop
    (varrayptr0_dep_outer x q)
    (R.ghost_vptr (Some?.v (snd0 x)).to `vdep` varrayptr0_dep_inner x q);
  let ar = elim_vdep (R.ghost_vptr (Some?.v (snd0 x)).to) (varrayptr0_dep_inner x q) in
  let res = Ghost.hide ((Some?.v (snd0 x)).to, Ghost.reveal ar) in
  change_equal_slprop
    (R.ghost_vptr (Some?.v (snd0 x)).to)
    (R.ghost_vptr (fst0 res));
  change_equal_slprop
    (varrayptr0_dep_inner x q ar)
    (A.varray (snd0 res));
  res
  
let is_arrayptr r = hp_of (varrayptr0 r)
let arrayptr_sel r = sel_of (varrayptr0 r)

val intro_varrayptr
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
  (ar: A.array base a)
  (sq: squash (g_is_null x == false))
: SteelGhost unit opened
    (R.ghost_vptr (Some?.v (snd0 x)).to `star` A.varray ar)
    (fun _ -> varrayptr x)
    (requires (fun h ->
      h (R.ghost_vptr (Some?.v (snd0 x)).to) == ar
    ))
    (ensures (fun h _ h' ->
      let res = h' (varrayptr x) in
      res.array == ar /\
      res.contents == h (A.varray ar)
    ))

let intro_varrayptr
  x ar sq
=
  intro_varrayptr0 x ar sq;
  change_slprop_rel
    (varrayptr0 x)
    (varrayptr x)
    (fun u v -> u == v)
    (fun m ->
      assert_norm (hp_of (varrayptr x) == hp_of (varrayptr0 x));
      assert_norm (sel_of (varrayptr x) m === sel_of (varrayptr0 x) m)
    )

val elim_varrayptr
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost (Ghost.erased (R.ghost_ref (array' (fst0 x)) & A.array base a)) opened
    (varrayptr x)
    (fun res -> R.ghost_vptr (fst0 res) `star` A.varray (snd0 res))
    (requires (fun _ -> True))
    (ensures (fun h res h' ->
      let pres = h (varrayptr x) in
      let ar = snd0 res in
      g_is_null x == false /\
      fst0 res == (Some?.v (snd0 x)).to /\
      pres.array == Ghost.reveal ar /\
      h' (R.ghost_vptr (fst0 res)) == Ghost.reveal ar /\
      h' (A.varray ar) == pres.contents
    ))

let elim_varrayptr
  #_ #base #a x
=
  change_slprop_rel
    (varrayptr x)
    (varrayptr0 x)
    (fun u v -> u == v)
    (fun m ->
      assert_norm (hp_of (varrayptr x) == hp_of (varrayptr0 x));
      assert_norm (sel_of (varrayptr x) m === sel_of (varrayptr0 x) m)
    );
  elim_varrayptr0 x

let varrayptr_not_null
  x
=
  let tmp = elim_varrayptr x in
  change_equal_slprop
    (R.ghost_vptr (fst0 tmp))
    (R.ghost_vptr (Some?.v (snd0 x)).to);
  intro_varrayptr x (snd0 tmp) ()

[@@__steel_reduce__]
let varrayptr_or_null0
  (#base #a: Type)
  (r: t base a)
: Tot vprop
= if g_is_null r
  then emp `vrewrite` (fun _ -> None <: option (v base a))
  else varrayptr r `vrewrite` Some

let is_arrayptr_or_null r = hp_of (varrayptr_or_null0 r)
let arrayptr_or_null_sel r = sel_of (varrayptr_or_null0 r)

let intro_varrayptr_or_null_none
  #_ #base #a x
=
  intro_vrewrite emp (fun _ -> None <: option (v base a));
  change_slprop_rel
    (emp `vrewrite` (fun _ -> None <: option (v base a)))
    (varrayptr_or_null x)
    (fun u v -> u == v)
    (fun _ -> ())

let intro_varrayptr_or_null_some
  #_ #base #a x
=
  intro_vrewrite (varrayptr x) Some;
  change_slprop_rel
    (varrayptr x `vrewrite` Some)
    (varrayptr_or_null x)
    (fun u v -> u == v)
    (fun _ -> ())

let elim_varrayptr_or_null_some
  #_ #base #a x
=
  if g_is_null x
  then begin
    change_slprop_rel
      (varrayptr_or_null x)
      (emp `vrewrite` (fun _ -> None <: option (v base a)))
      (fun u v -> u == v)
      (fun _ -> ());
    elim_vrewrite
      emp
      (fun _ -> None <: option (v base a));
    assert False;
    change_equal_slprop
      emp
      (varrayptr x)
  end else begin
    change_slprop_rel
      (varrayptr_or_null x)
      (varrayptr x `vrewrite` Some)
      (fun u v -> u == v)
      (fun _ -> ());
    elim_vrewrite (varrayptr x) Some
  end

let elim_varrayptr_or_null_none
  #_ #base #a x
=
  if g_is_null x
  then begin
    change_slprop_rel
      (varrayptr_or_null x)
      (emp `vrewrite` (fun _ -> None <: option (v base a)))
      (fun u v -> u == v)
      (fun _ -> ());
    elim_vrewrite
      emp
      (fun _ -> None <: option (v base a))
  end else begin
    change_slprop_rel
      (varrayptr_or_null x)
      (varrayptr x `vrewrite` Some)
      (fun u v -> u == v)
      (fun _ -> ());
    elim_vrewrite (varrayptr x) Some;
    assert False;
    change_equal_slprop
      (varrayptr x)
      emp
  end

let ghost_vptr_or_none
  (#a: Type)
  (r: option (R.ghost_ref a))
: Tot vprop
= if None? r
  then emp
  else R.ghost_vptr (Some?.v r)

let array_or_null_of_intro
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost (Ghost.erased (A.array_or_null base a & option (R.ghost_ref (array' (fst0 x))))) opened
    (varrayptr_or_null x)
    (fun res -> A.varray_or_null (fst0 res) `star` ghost_vptr_or_none (snd0 res))
    (fun _ -> True)
    (fun h res h' ->
      let z : option (v base a) = h (varrayptr_or_null x) in
      fst0 (fst0 res) == fst0 x /\
      (None? z <==> g_is_null x) /\
      (None? z <==> A.g_is_null (fst0 res)) /\
      (None? z <==> None? (snd0 res)) /\
      (Some? z ==> (
        Some?.v (snd0 res) == (Some?.v (snd0 x)).to /\
        (h' (R.ghost_vptr (Some?.v (snd0 res))) <: A.array_or_null base a) == fst0 res /\
        (Some?.v z).array == fst0 res /\
        (Some?.v z).contents == h' (A.varray (fst0 res))
      ))
    )
=
  if g_is_null x
  then begin
    elim_varrayptr_or_null_none x;
    let res = (A.null base a, None) in
    change_equal_slprop
      emp
      (A.varray_or_null (fst0 res));
    change_equal_slprop
      emp
      (ghost_vptr_or_none (snd0 res));
    res
  end else begin
    elim_varrayptr_or_null_some x;
    let tmp = elim_varrayptr x in
    let res = (snd0 tmp, Some (fst0 tmp)) in
    change_equal_slprop
      (R.ghost_vptr (fst0 tmp))
      (ghost_vptr_or_none (snd0 res));
    change_equal_slprop
      (A.varray (snd0 tmp))
      (A.varray_or_null (fst0 res));
    res
  end

let array_or_null_of_elim
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
  (res: Ghost.erased (A.array_or_null base a & option (R.ghost_ref (array' (fst0 x)))))
: SteelGhost unit opened
    (A.varray_or_null (fst0 res) `star` ghost_vptr_or_none (snd0 res))
    (fun _ -> varrayptr_or_null x)
    (fun h ->
      fst0 (fst0 res) == fst0 x /\
      (g_is_null x <==> A.g_is_null (fst0 res)) /\
      (g_is_null x <==> None? (snd0 res)) /\
      (Some? (snd0 res) ==> (
        Some?.v (snd0 res) == (Some?.v (snd0 x)).to /\
        (h (R.ghost_vptr (Some?.v (snd0 res))) <: A.array_or_null base a) == fst0 res
      ))
    )
    (fun h _ h' ->
      let z : option (v base a) = h' (varrayptr_or_null x) in
      fst0 (fst0 res) == fst0 x /\
      (None? z <==> g_is_null x) /\
      (None? z <==> A.g_is_null (fst0 res)) /\
      (None? z <==> None? (snd0 res)) /\
      (Some? z ==> (
        (h (R.ghost_vptr (Some?.v (snd0 res))) <: A.array_or_null base a) == fst0 res /\
        (Some?.v z).array == fst0 res /\
        (Some?.v z).contents == h (A.varray (fst0 res))
      ))
    )
= if g_is_null x
  then begin
    change_equal_slprop
      (A.varray_or_null (fst0 res))
      emp;
    change_equal_slprop
      (ghost_vptr_or_none (snd0 res))
      emp;
    intro_varrayptr_or_null_none x
  end else begin
    let ar : A.array base a = fst0 res in
    change_equal_slprop
      (A.varray_or_null (fst0 res))
      (A.varray ar);
    change_equal_slprop
      (ghost_vptr_or_none (snd0 res))
      (R.ghost_vptr (Some?.v (snd0 x)).to);
    intro_varrayptr x ar ();
    intro_varrayptr_or_null_some x
  end

let is_null #base #a x
=
  let tmp = array_or_null_of_intro x in
  let ar : (ar: A.array_or_null base a { ar == fst0 tmp }) =
    (fst0 x, snd0 (fst0 tmp))
  in
  change_equal_slprop
     (A.varray_or_null (fst0 tmp))
     (A.varray_or_null ar);
  let res = A.is_null ar in
  change_equal_slprop
    (A.varray_or_null ar)
    (A.varray_or_null (fst0 tmp));
  array_or_null_of_elim x tmp;
  return res

let adjacent x1 x2 = A.adjacent x1 x2
let merge x1 x2 = A.merge x1 x2

let join al ar =
  let tmpr = elim_varrayptr ar in
  R.ghost_free (fst0 tmpr);
  let tmpl = elim_varrayptr al in
  let res = A.join' (snd0 tmpl) (snd0 tmpr) in
  R.ghost_write (fst0 tmpl) (Ghost.reveal res);
  change_equal_slprop
    (R.ghost_vptr (fst0 tmpl))
    (R.ghost_vptr (Some?.v (snd0 al)).to);
  intro_varrayptr al res ()
