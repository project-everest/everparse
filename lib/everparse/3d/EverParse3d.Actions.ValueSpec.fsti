module EverParse3d.Actions.ValueSpec

(* Value-level semantics of 3d actions.

   `EverParse3d.Actions.Spec` specifies validators at the byte level: a
   `vspec` reads the input bytes. This module specifies the effect of actions
   in terms of the *parsed value* instead: a `value_spec d t` takes the
   position at which the value starts, a value `v: t` and the action state
   before validation, and returns whether the actions succeed, along with the
   final action state.

   The link between the two levels is `vspec_refines p s vs`: whenever the
   parser `p` succeeds on the input with value `v`, the byte-level spec `s`
   coincides with the value-level spec `vs` on `v`. Positions of fields are
   computed from the parsed values with `vsize`, the number of bytes consumed
   by the parser on a given value, which is well defined since all 3d parsers
   are injective.

   For each validator spec combinator of `EverParse3d.Actions.Spec`, this
   module provides a value spec combinator and a lemma stating that the
   refinement is preserved. Those lemmas are assembled into a proof by
   induction on 3d types in `EverParse3d.Interpreter`. *)

open EverParse3d.State
module S = EverParse3d.Actions.Spec
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Spec.List
module LUT = LowParse.Spec.ListUpTo
module FLD = LowParse.Spec.FLData
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

(** Value specs *)

let value_spec (d: state_dict) (t: Type0) : Type0 =
  nat -> t -> forevery_values d -> GTot (S.spec_res d bool)

(* The validation result corresponding to the result of the actions. *)
let vres_of_sres (#d: state_dict) (r: S.spec_res d bool) : GTot (S.vres d) =
  match r with
  | S.SOk true s -> S.VOk s
  | S.SOk false _ -> S.VErr
  | S.SUnknown -> S.VUnknown

(* Sequential composition: continue with `k` only if the actions so far have
   succeeded. *)
let sres_then (#d: state_dict) (r: S.spec_res d bool) (k: forevery_values d -> GTot (S.spec_res d bool)) : GTot (S.spec_res d bool) =
  match r with
  | S.SOk true s -> k s
  | _ -> r

(* The number of bytes consumed by the parser `p` when it returns `v`. *)
val vsize
  (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (v: t)
: GTot nat

val vsize_eq
  (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (b: LP.bytes)
: Lemma
  (match P.parse p b with
   | Some (v, n) -> vsize p v == n
   | None -> True)

(** Refinement *)

let vinput_ok (i: S.vinput) : prop =
  Seq.length i.S.rest <= Seq.length i.S.contents

let refines_at
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (i: S.vinput) (x: forevery_values d)
: prop
= vinput_ok i ==> (match P.parse p i.S.rest with
  | Some (v, _) -> s i x == vres_of_sres (vs (S.vpos i) v x)
  | None -> True)

(* Whenever `p` succeeds on the remaining input with a value `v`, the
   byte-level spec `s` is determined by the value-level spec `vs` on `v`,
   started at the current position. *)
let vspec_refines
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: prop
= forall (i: S.vinput) (x: forevery_values d) . refines_at p s vs i x

let pure_at (#d: state_dict) (#t: Type0) (vs: value_spec d t) (pos: nat) (v: t) (x: forevery_values d) : prop =
  vs pos v x == S.SOk true x

(* A value spec without actions. *)
let value_spec_pure (#d: state_dict) (#t: Type0) (vs: value_spec d t) : prop =
  forall (pos: nat) (v: t) (x: forevery_values d) . pure_at vs pos v x

(* The invariant of the value spec of a type: it refines the byte-level spec,
   and it has no effect if the type has no actions. *)
let vspec_wf
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: prop
= vspec_refines p s vs /\ (ha == false ==> value_spec_pure vs)

(** Inputs *)

(** Combinators *)

(* No actions. Also the value spec of `T_false`, whose parser always fails. *)
let vs_true (#d: state_dict) (#t: Type0) : value_spec d t =
  fun _ _ x -> S.SOk true x

val wf_of_parser
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
: Lemma (vspec_wf ha p (S.vspec_of_parser #d p) (vs_true #d #t))

(* Weakening the kind of a parser. *)
val wf_weaken_left
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
  (#nz': bool) (#wk': P.weak_kind) (k': P.parser_kind nz' wk')
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_weaken_left p k') s vs))

val wf_weaken_right
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
  (#nz': bool) (#wk': P.weak_kind) (k': P.parser_kind nz' wk')
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_weaken_right p k') s vs))

val wf_ha
  (#d: state_dict) (ha ha': bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs /\ (ha' == false ==> ha == false)))
  (ensures (vspec_wf ha' p s vs))

(* Weakening the action state *)

let vs_weaken
  (#d1: state_dict) (#t: Type0) (vs: value_spec d1 t)
  (d2: state_dict) (sq: squash (state_dict_weaken_prop d1 d2))
: value_spec d2 t
= fun pos v x2 -> match vs pos v (mk_proj_value x2 d1 sq) with
  | S.SOk b x1' -> S.SOk b (S.weaken_update d1 d2 sq x2 x1')
  | S.SUnknown -> S.SUnknown

val weaken_update_proj
  (d1 d2: state_dict)
  (sq: squash (state_dict_weaken_prop d1 d2))
  (x2: forevery_values d2)
: Lemma (S.weaken_update d1 d2 sq x2 (mk_proj_value x2 d1 sq) == x2)

val wf_weaken
  (#d1: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d1) (vs: value_spec d1 t)
  (d2: state_dict) (sq: squash (state_dict_weaken_prop d1 d2))
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha p (S.vspec_weaken s d2 sq) (vs_weaken vs d2 sq)))

(* Pairs *)

let vs_pair
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (vs1: value_spec d t1) (#t2: Type0) (vs2: value_spec d t2)
: value_spec d (t1 & t2)
= fun pos v x -> sres_then (vs1 pos (fst v) x) (fun x1 -> vs2 (pos + vsize p1 (fst v)) (snd v) x1)

val wf_pair
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (k1_const: bool) (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: Type0) (p2: P.parser k2 t2)
  (k2_const: bool) (ha2: bool) (s2: S.vspec d) (vs2: value_spec d t2)
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ vspec_wf ha2 p2 s2 vs2))
  (ensures (vspec_wf (ha1 || ha2) (P.parse_pair p1 p2) (S.vspec_pair p1 k1_const ha1 s1 p2 k2_const ha2 s2) (vs_pair p1 vs1 vs2)))

(* Dependent pairs *)

let vs_dep_pair
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (vs1: value_spec d t1) (#t2: t1 -> Type0) (vs2: (x: t1) -> value_spec d (t2 x))
: value_spec d (dtuple2 t1 t2)
= fun pos v x -> sres_then (vs1 pos (dfst v) x) (fun x1 -> vs2 (dfst v) (pos + vsize p1 (dfst v)) (dsnd v) x1)

val wf_dep_pair
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: t1 -> S.vspec d) (vs2: (x: t1) -> value_spec d (t2 x))
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ (forall (y: t1) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y))))
  (ensures (vspec_wf (ha1 || ha2) (P.parse_dep_pair p1 p2) (S.vspec_dep_pair p1 s1 s2) (vs_dep_pair p1 vs1 vs2)))

let vs_dep_pair_with_action
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (vs1: value_spec d t1) (a: t1 -> S.action_spec d bool) (#t2: t1 -> Type0) (vs2: (x: t1) -> value_spec d (t2 x))
: value_spec d (dtuple2 t1 t2)
= fun pos v x -> sres_then (vs1 pos (dfst v) x) (fun x1 ->
    sres_then (a (dfst v) ({ S.a_start = pos }) x1) (fun x2 ->
    vs2 (dfst v) (pos + vsize p1 (dfst v)) (dsnd v) x2))

val wf_dep_pair_with_action
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (a: t1 -> S.action_spec d bool)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: t1 -> S.vspec d) (vs2: (x: t1) -> value_spec d (t2 x))
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ (forall (y: t1) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y))))
  (ensures (vspec_wf true (P.parse_dep_pair p1 p2) (S.vspec_dep_pair_with_action p1 s1 a s2) (vs_dep_pair_with_action p1 vs1 a vs2)))

(* Refinements *)

let vs_action_opt
  (#d: state_dict) (#t: Type0) (a: option (t -> S.action_spec d bool)) (pos: nat) (v: t) (x: forevery_values d)
: GTot (S.spec_res d bool)
= match a with
  | None -> S.SOk true x
  | Some a -> a v ({ S.a_start = pos }) x

let vs_filter
  (#d: state_dict) (#t: Type0) (vs: value_spec d t) (f: t -> bool) (a: option (t -> S.action_spec d bool))
: value_spec d (P.refine t f)
= fun pos v x -> sres_then (vs pos v x) (fun x1 -> vs_action_opt a pos v x1)

val wf_filter
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (f: t -> bool) (a: option (t -> S.action_spec d bool))
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf (ha || Some? a) (P.parse_filter p f) (S.vspec_filter p s f a) (vs_filter vs f a)))

let vs_dep_pair_with_refinement
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (vs1: value_spec d t1) (f: t1 -> bool) (a: option (t1 -> S.action_spec d bool))
  (#t2: P.refine t1 f -> Type0) (vs2: (x: P.refine t1 f) -> value_spec d (t2 x))
: value_spec d (dtuple2 (P.refine t1 f) t2)
= fun pos v x -> sres_then (vs1 pos (dfst v) x) (fun x1 ->
    sres_then (vs_action_opt a pos (dfst v) x1) (fun x2 ->
    vs2 (dfst v) (pos + vsize p1 (dfst v)) (dsnd v) x2))

val wf_dep_pair_with_refinement
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (f: t1 -> bool) (a: option (t1 -> S.action_spec d bool))
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: P.refine t1 f -> Type0) (p2: (x: P.refine t1 f) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: P.refine t1 f -> S.vspec d) (vs2: (x: P.refine t1 f) -> value_spec d (t2 x))
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ (forall (y: P.refine t1 f) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y))))
  (ensures (vspec_wf (ha1 || ha2 || Some? a) (P.parse_dep_pair (P.parse_filter p1 f) p2)
    (S.vspec_dep_pair_with_refinement_gen (not ha1) p1 s1 f a s2)
    (vs_dep_pair_with_refinement p1 vs1 f a vs2)))

(* Conditionals *)

let vs_ite
  (#d: state_dict) (e: bool)
  (#a1: squash e -> Type0) (#a2: squash (not e) -> Type0)
  (vs1: (sq: squash e) -> value_spec d (a1 sq))
  (vs2: (sq: squash (not e)) -> value_spec d (a2 sq))
: value_spec d (P.t_ite e a1 a2)
= fun pos v x -> if e then vs1 () pos (coerce_eq () v) x else vs2 () pos (coerce_eq () v) x

val wf_ite
  (#d: state_dict) (ha: bool) (e: bool)
  (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk)
  (#a1: squash e -> Type0) (#a2: squash (not e) -> Type0)
  (p1: (sq: squash e) -> P.parser k (a1 sq))
  (p2: (sq: squash (not e)) -> P.parser k (a2 sq))
  (s1: squash e -> S.vspec d) (s2: squash (not e) -> S.vspec d)
  (vs1: (sq: squash e) -> value_spec d (a1 sq))
  (vs2: (sq: squash (not e)) -> value_spec d (a2 sq))
: Lemma
  (requires (
    (e == true ==> vspec_wf ha (p1 ()) (s1 ()) (vs1 ())) /\
    (e == false ==> vspec_wf ha (p2 ()) (s2 ()) (vs2 ()))
  ))
  (ensures (vspec_wf ha (P.parse_ite e p1 p2) (S.vspec_ite e s1 s2) (vs_ite e vs1 vs2)))

(* Actions attached to a field *)

let vs_with_action
  (#d: state_dict) (#t: Type0) (vs: value_spec d t) (a: S.action_spec d bool)
: value_spec d t
= fun pos v x -> sres_then (vs pos v x) (fun x1 -> a ({ S.a_start = pos }) x1)

val wf_with_action
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (a: S.action_spec d bool)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf true p (S.vspec_with_success_action p s a) (vs_with_action vs a)))

let vs_with_dep_action
  (#d: state_dict) (#t: Type0) (vs: value_spec d t) (a: t -> S.action_spec d bool)
: value_spec d t
= fun pos v x -> sres_then (vs pos v x) (fun x1 -> a v ({ S.a_start = pos }) x1)

val wf_with_dep_action
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (a: t -> S.action_spec d bool)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf true p (S.vspec_with_dep_action p s a) (vs_with_dep_action vs a)))

(* Fixed-size data *)

val vs_t_exact
  (#d: state_dict) (n: U32.t) (#t: Type0) (vs: value_spec d t)
: value_spec d (P.t_exact n t)

val wf_t_exact
  (#d: state_dict) (ha: bool) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_t_exact n p) (S.vspec_t_exact n p s) (vs_t_exact n vs)))

val vs_t_at_most
  (#d: state_dict) (n: U32.t) (#t: Type0) (vs: value_spec d t)
: value_spec d (P.t_at_most n t)

val wf_t_at_most
  (#d: state_dict) (ha: bool) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_t_at_most n p) (S.vspec_t_at_most n s) (vs_t_at_most n vs)))

(* Lists *)

let rec vs_list
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (vs: value_spec d t) (pos: nat) (l: list t) (x: forevery_values d)
: GTot (S.spec_res d bool) (decreases l)
= match l with
  | [] -> S.SOk true x
  | v :: tl -> sres_then (vs pos v x) (fun x1 -> vs_list p vs (pos + vsize p v) tl x1)

val vs_list_pure
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (vs: value_spec d t) (pos: nat) (l: list t) (x: forevery_values d)
: Lemma
  (requires (value_spec_pure vs))
  (ensures (vs_list p vs pos l x == S.SOk true x))

val vs_nlist
  (#d: state_dict) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (vs: value_spec d t)
: value_spec d (P.nlist n t)

val wf_nlist
  (#d: state_dict) (ha: bool)
  (n: U32.t) (n_is_const: option nat { P.memoizes_n_as_const n_is_const n })
  (#wk: P.weak_kind) (#k: P.parser_kind true wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_nlist n n_is_const p) (S.vspec_nlist ha n n_is_const p s) (vs_nlist n p vs)))

(* Strings *)

val string_elem (#t: eqtype) (terminator: t) : Type0

val vs_string
  (#d: state_dict) (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (vs: value_spec d t)
: value_spec d (P.cstring t terminator)

val wf_string
  (#d: state_dict) (ha: bool)
  (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_string p terminator) (S.vspec_string ha p terminator s) (vs_string p terminator vs)))

(** Client-facing corollary *)

(* If the parser succeeds with value `v`, then validation succeeds with final
   action state `x'` iff the value spec of `v` returns `SOk true x'`, fails if
   it returns `SOk false _`, and is unspecified if it returns `SUnknown`. *)
val vspec_wf_elim
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (vspec_wf ha p s vs /\ vinput_ok i))
  (ensures (match P.parse p i.S.rest with
    | Some (v, _) -> s i x == vres_of_sres (vs (S.vpos i) v x)
    | None -> True))
