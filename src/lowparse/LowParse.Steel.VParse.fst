module LowParse.Steel.VParse
include LowParse.Spec.Base

module S = Steel.Memory
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.C.Array
module AP = LowParse.Steel.ArrayPtr

let is_byte_repr_injective
  #k #t p x b1 b2
= parse_injective p b1 b2

let cvalid
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (c: AP.v base byte)
: Tot prop
= valid p c.AP.contents /\
  array_prop k c.AP.array

unfold
let intro_cvalid
  (#base: Type)
  (a: byte_array base)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (c: AP.v base byte)
  (sq: squash (cvalid p c))
: Tot (SE.t_of (AP.varrayptr a `SE.vrefine` cvalid p))
= c

let select
  (#base: Type)
  (a: byte_array base)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: SE.t_of (AP.varrayptr a `SE.vrefine` cvalid p))
: GTot (v base k t)
=
  let x : AP.v base byte = x in
  let Some (y, _) = parse p x.AP.contents in
  {
    array_perm = (x.AP.array); // , x.AP.perm);
    contents = y;
    array_perm_prf = ();
  }

let select_correct
  (#base: Type)
  (a: byte_array base)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: SE.normal (SE.t_of (AP.varrayptr a `SE.vrefine` cvalid p)))
: Lemma
  (is_byte_repr p (select a p x).contents x.AP.contents)
= ()

let vparse0
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: Pure SE.vprop
  (requires True)
  (ensures (fun y -> SE.t_of y == v base k t))
= (AP.varrayptr a `SE.vrefine` cvalid p) `SE.vrewrite`  select a p

unfold
let vparse0_sel
  (#p:SE.vprop)
  (#base: Type)
  (#k: parser_kind) (#t: Type) (q: parser k t)
  (r:byte_array base)
  (h:SE.rmem p{FStar.Tactics.with_tactic SE.selector_tactic (SE.can_be_split p (vparse0 q r) /\ True)})
: GTot (v base k t)
= let x : (SE.t_of (vparse0 q r)) =
    h (vparse0 q r)
  in
  x

let intro_vparse0
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: SEA.SteelGhost unit opened
    (AP.varrayptr a)
    (fun _ -> vparse0 p a)
    (fun h ->
      valid p (h (AP.varrayptr a)).AP.contents
    )
    (fun h _ h' ->
      valid p (h (AP.varrayptr a)).AP.contents /\
//      perm_of (vparse0_sel p a h') == (h (AP.varrayptr a)).AP.perm /\
      array_of (vparse0_sel p a h') == (h (AP.varrayptr a)).AP.array /\
      is_byte_repr p (vparse0_sel p a h').contents (h (AP.varrayptr a)).AP.contents
    )
=
  parser_kind_prop_equiv k p;
  SEA.intro_vrefine (AP.varrayptr a) (cvalid p);
  SEA.intro_vrewrite (AP.varrayptr a `SE.vrefine` cvalid p) (select a p);
  assert_norm ((AP.varrayptr a `SE.vrefine` cvalid p) `SE.vrewrite` select a p == vparse0 p a); // FIXME: WHY WHY WHY?
  SEA.change_equal_slprop ((AP.varrayptr a `SE.vrefine` cvalid p) `SE.vrewrite` select a p) (vparse0 p a)

let change_equal_slprop (#opened: _) (p q: SE.vprop)
  (sq: squash (p == q))
  : SEA.SteelGhost unit opened p (fun _ -> q) (fun _ -> True) (fun h0 _ h1 -> p == q /\ h1 q == h0 p)
= SEA.change_equal_slprop p q

let elim_vparse0
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: SEA.SteelGhost unit opened
    (vparse0 p a)
    (fun _ -> AP.varrayptr a)
    (fun _ -> True)
    (fun h _ h' ->
      (h' (AP.varrayptr a)).AP.array == array_of (vparse0_sel p a h) /\
//      (h' (AP.varrayptr a)).AP.perm == perm_of (vparse0_sel p a h) /\
      valid p (h' (AP.varrayptr a)).AP.contents /\
      is_byte_repr p (vparse0_sel p a h).contents (h' (AP.varrayptr a)).AP.contents
    )
=
  let sq : squash (vparse0 #base #k #t p a == (AP.varrayptr a `SE.vrefine` cvalid p) `SE.vrewrite` select a p) =
    assert_norm (vparse0 #base #k #t p a == (AP.varrayptr a `SE.vrefine` cvalid p) `SE.vrewrite` select a p)
  in
  change_equal_slprop (vparse0 #base #k #t p a)
    ((AP.varrayptr a `SE.vrefine` cvalid p) `SE.vrewrite` select a p)
    sq;
  SEA.elim_vrewrite (AP.varrayptr a `SE.vrefine` cvalid p) (select a p);
  let g = SEA.gget (AP.varrayptr a `SE.vrefine` cvalid p) in
  assert (valid p (Ghost.reveal g <: AP.v base byte).AP.contents);
  SEA.elim_vrefine (AP.varrayptr a) (cvalid p)

let vparse_slprop
  #base #k #t p a
=
  SE.hp_of (vparse0 #base #k #t p a)

let vparse_sel
  p a
=
  SE.sel_of (vparse0 p a)

let intro_vparse
  #opened #base #k #t p a
=
  intro_vparse0 p a;
  SEA.change_slprop_rel
    (vparse0 p a)
    (vparse p a)
    (fun (x: SE.t_of (vparse0 p a)) (y: SE.t_of (vparse p a)) -> (x <: v base k t) == y)
    (fun _ -> ());
  ()

let elim_vparse
  #opened #base #k #t p a
=
  SEA.change_slprop_rel
    (vparse p a)
    (vparse0 p a)
    (fun (x: SE.t_of (vparse p a)) (y: SE.t_of (vparse0 p a)) -> (x <: v base k t) == y)
    (fun _ -> ());
  elim_vparse0 p a

(*
let share
  p a
=
  elim_vparse p a;
  let g0 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY?
  let res = AP.share a in
  intro_vparse p a;
  intro_vparse p res;
  SEA.return res

let gather
  #k #t p a1 a2
=
  elim_vparse p a1;
  let g0 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a1) in // FIXME: WHY WHY WHY?  
  elim_vparse p a2;
  AP.gather a1 a2;
  intro_vparse p a1
*)
