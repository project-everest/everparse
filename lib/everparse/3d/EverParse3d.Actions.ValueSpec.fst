module EverParse3d.Actions.ValueSpec

friend EverParse3d.Prelude

open EverParse3d.State
module S = EverParse3d.Actions.Spec
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module PM = EverParse3d.PtrModel
module LPL = LowParse.Spec.List
module LUT = LowParse.Spec.ListUpTo
module FLD = LowParse.Spec.FLData
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

let parses_to
  (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (v: t) (b: LP.bytes)
: prop
= match P.parse p b with
  | Some (v', _) -> v' == v
  | None -> False

let vsize
  (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (v: t)
: GTot nat
= if FStar.IndefiniteDescription.strong_excluded_middle (exists (b: LP.bytes) . parses_to p v b)
  then
    let b = FStar.IndefiniteDescription.indefinite_description_ghost LP.bytes (fun b -> parses_to p v b) in
    match P.parse p b with
    | Some (_, n) -> n
    | None -> 0
  else 0

let vsize_eq
  (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (b: LP.bytes)
: Lemma
  (match P.parse p b with
   | Some (v, n) -> vsize p v == n
   | None -> True)
= match P.parse p b with
  | Some (v, n) ->
    assert (parses_to p v b);
    let b' = FStar.IndefiniteDescription.indefinite_description_ghost LP.bytes (fun b -> parses_to p v b) in
    LP.parser_kind_prop_equiv k p;
    assert (LP.injective_precond #t p b' b)
  | None -> ()

let intro_refines
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
  (f: (i: S.vinput) -> (x: forevery_values d) -> Lemma
    (requires (vinput_ok i))
    (ensures (refines_at p s vs i x)))
: Lemma (vspec_refines p s vs)
= introduce forall (i: S.vinput) (x: forevery_values d) . refines_at p s vs i x
  with (
    introduce vinput_ok i ==> refines_at p s vs i x
    with f i x
  )

let intro_pure
  (#d: state_dict) (#t: Type0) (vs: value_spec d t)
  (f: (pos: S.aenv) -> (v: t) -> (x: forevery_values d) -> Lemma (pure_at vs pos v x))
: Lemma (value_spec_pure vs)
= introduce forall (pos: S.aenv) (v: t) (x: forevery_values d) . pure_at vs pos v x
  with f pos v x

let elim_refines
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (vspec_refines p s vs))
  (ensures (refines_at p s vs i x))
= ()

let elim_pure
  (#d: state_dict) (#t: Type0) (vs: value_spec d t) (pos: S.aenv) (v: t) (x: forevery_values d)
: Lemma
  (requires (value_spec_pure vs))
  (ensures (vs pos v x == S.VOk x))
= assert (pure_at vs pos v x)

let vpos_vadvance (i: S.vinput) (n: nat { n <= Seq.length i.S.rest })
: Lemma
  (requires (vinput_ok i))
  (ensures (
    vinput_ok (S.vadvance i n) /\
    S.vpos (S.vadvance i n) == S.vpos i + n /\
    S.venv (S.vadvance i n) == S.aenv_adv (S.venv i) n /\
    (S.vadvance i n).S.rest == Seq.slice i.S.rest n (Seq.length i.S.rest)
  ))
= ()

let vpos_vtruncate (i: S.vinput) (n: nat { n <= Seq.length i.S.rest })
: Lemma
  (requires (vinput_ok i))
  (ensures (
    vinput_ok (S.vtruncate i n) /\
    S.vpos (S.vtruncate i n) == S.vpos i /\
    S.venv (S.vtruncate i n) == S.venv i /\
    (S.vtruncate i n).S.rest == Seq.slice i.S.rest 0 n
  ))
= ()

let wf_of_parser
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
: Lemma (vspec_wf ha p (S.vspec_of_parser #d p) (vs_true #d #t))
= intro_refines p (S.vspec_of_parser #d p) (vs_true #d #t) (fun i x -> ());
  intro_pure (vs_true #d #t) (fun _ _ _ -> ())

let wf_of_parser_pure
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (vs: value_spec d t)
: Lemma
  (requires (value_spec_pure vs))
  (ensures (vspec_wf false p (S.vspec_of_parser #d p) vs))
= intro_refines p (S.vspec_of_parser #d p) vs (fun i x ->
    match P.parse p i.S.rest with
    | Some (v, _) -> elim_pure vs (S.venv i) v x
    | None -> ())

let wf_weaken_left
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
  (#nz': bool) (#wk': P.weak_kind) (k': P.parser_kind nz' wk')
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_weaken_left p k') s vs))
= intro_refines (P.parse_weaken_left p k') s vs (fun i x -> elim_refines p s vs i x)

let wf_weaken_right
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
  (#nz': bool) (#wk': P.weak_kind) (k': P.parser_kind nz' wk')
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_weaken_right p k') s vs))
= intro_refines (P.parse_weaken_right p k') s vs (fun i x -> elim_refines p s vs i x)

let wf_ha
  (#d: state_dict) (ha ha': bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs /\ (ha' == false ==> ha == false)))
  (ensures (vspec_wf ha' p s vs))
= ()

let weaken_update_proj
  (d1 d2: state_dict)
  (sq: squash (state_dict_weaken_prop d1 d2))
  (x2: forevery_values d2)
: Lemma (S.weaken_update d1 d2 sq x2 (mk_proj_value x2 d1 sq) == x2)
= let aux (x: string { state_p d2 x }) : Lemma
    (S.weaken_update d1 d2 sq x2 (mk_proj_value x2 d1 sq) x == x2 x)
  = if d1.state_p x
    then S.weaken_update_in d1 d2 sq x2 (mk_proj_value x2 d1 sq) x
    else S.weaken_update_out d1 d2 sq x2 (mk_proj_value x2 d1 sq) x
  in
  Classical.forall_intro aux;
  forevery_values_ext d2 (S.weaken_update d1 d2 sq x2 (mk_proj_value x2 d1 sq)) x2

let wf_weaken
  (#d1: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d1) (vs: value_spec d1 t)
  (d2: state_dict) (sq: squash (state_dict_weaken_prop d1 d2))
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha p (S.vspec_weaken s d2 sq) (vs_weaken vs d2 sq)))
= intro_refines p (S.vspec_weaken s d2 sq) (vs_weaken vs d2 sq) (fun i x2 ->
    elim_refines p s vs i (mk_proj_value x2 d1 sq)
  );
  if ha then () else
  intro_pure (vs_weaken vs d2 sq) (fun pos v x2 ->
    elim_pure vs pos v (mk_proj_value x2 d1 sq);
    weaken_update_proj d1 d2 sq x2
  )

let wf_pair_slow_at
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: Type0) (p2: P.parser k2 t2)
  (ha2: bool) (s2: S.vspec d) (vs2: value_spec d t2)
  (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (
    vspec_wf ha1 p1 s1 vs1 /\ vspec_wf ha2 p2 s2 vs2 /\
    vinput_ok i
  ))
  (ensures (refines_at (P.parse_pair p1 p2) (S.vspec_pair_slow p1 s1 s2) (vs_pair p1 vs1 vs2) i x))
= LPC.nondep_then_eq p1 p2 i.S.rest;
  elim_refines p1 s1 vs1 i x;
  match P.parse p1 i.S.rest with
  | None -> ()
  | Some (v1, n1) ->
  vsize_eq p1 i.S.rest;
  vpos_vadvance i n1;
  match vs1 (S.venv i) v1 x with
  | S.VOk x1 -> elim_refines p2 s2 vs2 (S.vadvance i n1) x1
  | _ -> ()

let wf_pair
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (k1_const: bool) (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: Type0) (p2: P.parser k2 t2)
  (k2_const: bool) (ha2: bool) (s2: S.vspec d) (vs2: value_spec d t2)
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ vspec_wf ha2 p2 s2 vs2))
  (ensures (vspec_wf (ha1 || ha2) (P.parse_pair p1 p2) (S.vspec_pair p1 k1_const ha1 s1 p2 k2_const ha2 s2) (vs_pair p1 vs1 vs2)))
= if ha1 || ha2 then () else
  intro_pure (vs_pair p1 vs1 vs2) (fun pos v x ->
    elim_pure vs1 pos (fst v) x;
    elim_pure vs2 (S.aenv_adv pos (vsize p1 (fst v))) (snd v) x
  );
  if k1_const && k2_const &&
     (not ha1) && (not ha2) &&
     k1.LP.parser_kind_high = Some k1.LP.parser_kind_low &&
     k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal &&
     k2.LP.parser_kind_high = Some k2.LP.parser_kind_low &&
     k2.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal &&
     k1.LP.parser_kind_low + k2.LP.parser_kind_low < 4294967296
  then wf_of_parser_pure (P.parse_pair p1 p2) (vs_pair p1 vs1 vs2)
  else intro_refines (P.parse_pair p1 p2) (S.vspec_pair_slow p1 s1 s2) (vs_pair p1 vs1 vs2)
    (wf_pair_slow_at p1 ha1 s1 vs1 p2 ha2 s2 vs2)

let wf_dep_pair_at
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: t1 -> S.vspec d) (vs2: (x: t1) -> value_spec d (t2 x))
  (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (
    vspec_wf ha1 p1 s1 vs1 /\ (forall (y: t1) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y)) /\
    vinput_ok i
  ))
  (ensures (refines_at (P.parse_dep_pair p1 p2) (S.vspec_dep_pair p1 s1 s2) (vs_dep_pair p1 vs1 vs2) i x))
= LPC.parse_dtuple2_eq p1 p2 i.S.rest;
  elim_refines p1 s1 vs1 i x;
  match P.parse p1 i.S.rest with
  | None -> ()
  | Some (v1, n1) ->
  vsize_eq p1 i.S.rest;
  vpos_vadvance i n1;
  match vs1 (S.venv i) v1 x with
  | S.VOk x1 -> elim_refines (p2 v1) (s2 v1) (vs2 v1) (S.vadvance i n1) x1
  | _ -> ()

let wf_dep_pair
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: t1 -> S.vspec d) (vs2: (x: t1) -> value_spec d (t2 x))
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ (forall (y: t1) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y))))
  (ensures (vspec_wf (ha1 || ha2) (P.parse_dep_pair p1 p2) (S.vspec_dep_pair p1 s1 s2) (vs_dep_pair p1 vs1 vs2)))
= intro_refines (P.parse_dep_pair p1 p2) (S.vspec_dep_pair p1 s1 s2) (vs_dep_pair p1 vs1 vs2)
    (wf_dep_pair_at p1 ha1 s1 vs1 p2 ha2 s2 vs2);
  if ha1 || ha2 then () else
  intro_pure (vs_dep_pair p1 vs1 vs2) (fun pos v x ->
    elim_pure vs1 pos (dfst v) x;
    elim_pure (vs2 (dfst v)) (S.aenv_adv pos (vsize p1 (dfst v))) (dsnd v) x
  )

let wf_dep_pair_with_action_at
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (a: t1 -> S.action_spec d bool)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: t1 -> S.vspec d) (vs2: (x: t1) -> value_spec d (t2 x))
  (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (
    vspec_wf ha1 p1 s1 vs1 /\ (forall (y: t1) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y)) /\
    vinput_ok i
  ))
  (ensures (refines_at (P.parse_dep_pair p1 p2) (S.vspec_dep_pair_with_action p1 s1 a s2) (vs_dep_pair_with_action p1 vs1 a vs2) i x))
= LPC.parse_dtuple2_eq p1 p2 i.S.rest;
  elim_refines p1 s1 vs1 i x;
  match P.parse p1 i.S.rest with
  | None -> ()
  | Some (v1, n1) ->
  vsize_eq p1 i.S.rest;
  vpos_vadvance i n1;
  match vs1 (S.venv i) v1 x with
  | S.VOk x1 ->
    begin match a v1 (S.venv i) x1 with
    | S.SOk true x2 -> elim_refines (p2 v1) (s2 v1) (vs2 v1) (S.vadvance i n1) x2
    | _ -> ()
    end
  | _ -> ()

let wf_dep_pair_with_action
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (a: t1 -> S.action_spec d bool)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: t1 -> S.vspec d) (vs2: (x: t1) -> value_spec d (t2 x))
: Lemma
  (requires (vspec_wf ha1 p1 s1 vs1 /\ (forall (y: t1) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y))))
  (ensures (vspec_wf true (P.parse_dep_pair p1 p2) (S.vspec_dep_pair_with_action p1 s1 a s2) (vs_dep_pair_with_action p1 vs1 a vs2)))
= intro_refines (P.parse_dep_pair p1 p2) (S.vspec_dep_pair_with_action p1 s1 a s2) (vs_dep_pair_with_action p1 vs1 a vs2)
    (wf_dep_pair_with_action_at p1 ha1 s1 vs1 a p2 ha2 s2 vs2)

let wf_filter
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (f: t -> bool) (a: option (t -> S.action_spec d bool))
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf (ha || Some? a) (P.parse_filter p f) (S.vspec_filter p s f a) (vs_filter vs f a)))
= intro_refines (P.parse_filter p f) (S.vspec_filter p s f a) (vs_filter vs f a) (fun i x ->
    LPC.parse_filter_eq p f i.S.rest;
    elim_refines p s vs i x
  );
  if ha || Some? a then () else
  intro_pure (vs_filter vs f a) (fun pos v x -> elim_pure vs pos v x)

#push-options "--z3rlimit 32"

let wf_dep_pair_with_refinement_at
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type0) (p1: P.parser k1 t1)
  (ha1: bool) (s1: S.vspec d) (vs1: value_spec d t1)
  (f: t1 -> bool) (a: option (t1 -> S.action_spec d bool))
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: P.refine t1 f -> Type0) (p2: (x: P.refine t1 f) -> P.parser k2 (t2 x))
  (ha2: bool) (s2: P.refine t1 f -> S.vspec d) (vs2: (x: P.refine t1 f) -> value_spec d (t2 x))
  (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (
    vspec_wf ha1 p1 s1 vs1 /\ (forall (y: P.refine t1 f) . vspec_wf ha2 (p2 y) (s2 y) (vs2 y)) /\
    vinput_ok i
  ))
  (ensures (refines_at (P.parse_dep_pair (P.parse_filter p1 f) p2)
    (S.vspec_dep_pair_with_refinement_gen (not ha1) p1 s1 f a s2)
    (vs_dep_pair_with_refinement p1 vs1 f a vs2) i x))
= LPC.parse_dtuple2_eq (P.parse_filter p1 f) p2 i.S.rest;
  LPC.parse_filter_eq p1 f i.S.rest;
  elim_refines p1 s1 vs1 i x;
  match P.parse p1 i.S.rest with
  | None -> ()
  | Some (v1, n1) ->
  vsize_eq p1 i.S.rest;
  vpos_vadvance i n1;
  if not ha1 then elim_pure vs1 (S.venv i) v1 x else ();
  if not (f v1) then () else
  match vs1 (S.venv i) v1 x with
  | S.VOk x1 ->
    begin match vs_action_opt a (S.venv i) v1 x1 with
    | S.VOk x2 -> elim_refines (p2 v1) (s2 v1) (vs2 v1) (S.vadvance i n1) x2
    | _ -> ()
    end
  | _ -> ()

#pop-options

let wf_dep_pair_with_refinement
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
= intro_refines (P.parse_dep_pair (P.parse_filter p1 f) p2)
    (S.vspec_dep_pair_with_refinement_gen (not ha1) p1 s1 f a s2)
    (vs_dep_pair_with_refinement p1 vs1 f a vs2)
    (wf_dep_pair_with_refinement_at p1 ha1 s1 vs1 f a p2 ha2 s2 vs2);
  if ha1 || ha2 || Some? a then () else
  intro_pure (vs_dep_pair_with_refinement p1 vs1 f a vs2) (fun pos v x ->
    elim_pure vs1 pos (dfst v) x;
    elim_pure (vs2 (dfst v)) (S.aenv_adv pos (vsize p1 (dfst v))) (dsnd v) x
  )

let wf_ite
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
= if e
  then begin
    intro_refines (P.parse_ite e p1 p2) (S.vspec_ite e s1 s2) (vs_ite e vs1 vs2) (fun i x ->
      elim_refines (p1 ()) (s1 ()) (vs1 ()) i x);
    if ha then () else
    intro_pure (vs_ite e vs1 vs2) (fun pos v x -> elim_pure (vs1 ()) pos (coerce_eq () v) x)
  end else begin
    intro_refines (P.parse_ite e p1 p2) (S.vspec_ite e s1 s2) (vs_ite e vs1 vs2) (fun i x ->
      elim_refines (p2 ()) (s2 ()) (vs2 ()) i x);
    if ha then () else
    intro_pure (vs_ite e vs1 vs2) (fun pos v x -> elim_pure (vs2 ()) pos (coerce_eq () v) x)
  end

let wf_with_action
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (a: S.action_spec d bool)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf true p (S.vspec_with_success_action p s a) (vs_with_action vs a)))
= intro_refines p (S.vspec_with_success_action p s a) (vs_with_action vs a) (fun i x ->
    elim_refines p s vs i x)

let wf_with_dep_action
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (a: t -> S.action_spec d bool)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf true p (S.vspec_with_dep_action p s a) (vs_with_dep_action vs a)))
= intro_refines p (S.vspec_with_dep_action p s a) (vs_with_dep_action vs a) (fun i x ->
    elim_refines p s vs i x)

let wf_with_dep_vaction
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (a: t -> S.vaction_spec d)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf true p (S.vspec_with_dep_vaction p s a) (vs_with_dep_vaction vs a)))
= intro_refines p (S.vspec_with_dep_vaction p s a) (vs_with_dep_vaction vs a) (fun i x ->
    elim_refines p s vs i x)

let parse_fldata_eq
  (#k: LP.parser_kind) (#t: Type) (p: LP.parser k t) (sz: nat) (input: LP.bytes)
: Lemma
  (LP.parse (FLD.parse_fldata p sz) input == (
    if Seq.length input < sz
    then None
    else match LP.parse p (Seq.slice input 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = sz then Some (v, (sz <: LP.consumed_length input)) else None
    | _ -> None
  ))
= ()

let vs_t_exact
  (#d: state_dict) (n: U32.t) (#t: Type0) (vs: value_spec d t)
: value_spec d (P.t_exact n t)
= fun pos v x -> vs pos v x

let wf_t_exact
  (#d: state_dict) (ha: bool) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_t_exact n p) (S.vspec_t_exact n p s) (vs_t_exact n vs)))
= intro_refines (P.parse_t_exact n p) (S.vspec_t_exact n p s) (vs_t_exact n vs) (fun i x ->
    parse_fldata_eq p (U32.v n) i.S.rest;
    if Seq.length i.S.rest < U32.v n then () else begin
    vpos_vtruncate i (U32.v n);
    elim_refines p s vs (S.vtruncate i (U32.v n)) x end);
  if ha then () else
  intro_pure (vs_t_exact n vs) (fun pos v x -> elim_pure vs pos v x)

let vs_t_at_most
  (#d: state_dict) (n: U32.t) (#t: Type0) (vs: value_spec d t)
: value_spec d (P.t_at_most n t)
= fun pos v x -> vs pos (fst v) x

let wf_t_at_most
  (#d: state_dict) (ha: bool) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_t_at_most n p) (S.vspec_t_at_most n s) (vs_t_at_most n vs)))
= intro_refines (P.parse_t_at_most n p) (S.vspec_t_at_most n s) (vs_t_at_most n vs) (fun i x ->
    parse_fldata_eq (LPC.nondep_then p P.parse_all_bytes) (U32.v n) i.S.rest;
    if Seq.length i.S.rest < U32.v n then () else begin
    LPC.nondep_then_eq p P.parse_all_bytes (Seq.slice i.S.rest 0 (U32.v n));
    vpos_vtruncate i (U32.v n);
    elim_refines p s vs (S.vtruncate i (U32.v n)) x end);
  if ha then () else
  intro_pure (vs_t_at_most n vs) (fun pos v x -> elim_pure vs pos (fst #t #P.all_bytes v) x)

let rec vs_list_pure
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (vs: value_spec d t) (pos: S.aenv) (l: list t) (x: forevery_values d)
: Lemma
  (requires (value_spec_pure vs))
  (ensures (vs_list p vs pos l x == S.VOk x))
  (decreases l)
= match l with
  | [] -> ()
  | v :: tl -> elim_pure vs pos v x; vs_list_pure p vs (S.aenv_adv pos (vsize p v)) tl x

#push-options "--z3rlimit 32"

let rec vspec_list_fold_eq
  (#d: state_dict) (#wk: P.weak_kind) (#k: P.parser_kind true wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (o: PM.ptr) (contents rest: Seq.seq U8.t) (x: forevery_values d)
: Lemma
  (requires (vspec_refines p s vs /\ Seq.length rest <= Seq.length contents))
  (ensures (match LP.parse (LPL.parse_list p) rest with
    | Some (l, _) -> S.vspec_list_fold p s o contents rest x == vs_list p vs ({ S.a_start = Seq.length contents - Seq.length rest; S.a_origin = o }) l x
    | None -> S.vspec_list_fold p s o contents rest x == S.VErr))
  (decreases (Seq.length rest))
= LPL.parse_list_eq p rest;
  if Seq.length rest = 0 then ()
  else
  let i = { S.contents = contents; S.rest = rest; S.origin = o } in
  elim_refines p s vs i x;
  match LP.parse p rest with
  | None -> ()
  | Some (v, n) ->
    vsize_eq p rest;
    if n = 0 then ()
    else begin
      let rest' = Seq.slice rest n (Seq.length rest) in
      match vs (S.venv i) v x with
      | S.VOk x1 -> vspec_list_fold_eq p s vs o contents rest' x1
      | _ -> ()
    end

#pop-options

let vs_nlist
  (#d: state_dict) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (vs: value_spec d t)
: value_spec d (P.nlist n t)
= fun pos l x -> vs_list p vs pos l x

let wf_nlist
  (#d: state_dict) (ha: bool)
  (n: U32.t) (n_is_const: option nat { P.memoizes_n_as_const n_is_const n })
  (#wk: P.weak_kind) (#k: P.parser_kind true wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_nlist n n_is_const p) (S.vspec_nlist ha n n_is_const p s) (vs_nlist n p vs)))
= if ha
  then
    intro_refines (P.parse_nlist n n_is_const p) (S.vspec_nlist ha n n_is_const p s) (vs_nlist n p vs) (fun i x ->
      parse_fldata_eq (LPL.parse_list p) (U32.v n) i.S.rest;
      if Seq.length i.S.rest < U32.v n then () else begin
      vpos_vtruncate i (U32.v n);
      let i' = S.vtruncate i (U32.v n) in
      LP.parser_kind_prop_equiv (LPL.parse_list_kind k.LP.parser_kind_injective) (LPL.parse_list p);
      vspec_list_fold_eq p s vs i'.S.origin i'.S.contents i'.S.rest x end)
  else begin
    intro_pure (vs_nlist n p vs) (fun pos l x -> vs_list_pure p vs pos l x);
    wf_of_parser_pure (P.parse_nlist n n_is_const p) (vs_nlist n p vs)
  end

let string_prf
  (#k: P.parser_kind true P.WeakKindStrongPrefix)
  (#t: eqtype)
  (p: P.parser k t)
  (terminator: t)
: Tot (LUT.consumes_if_not_cond (P.cond_string_up_to terminator) p)
= LP.parser_kind_prop_equiv k p;
  (fun _ _ _ -> ())

let parse_string_eq
  (#k: P.parser_kind true P.WeakKindStrongPrefix)
  (#t: eqtype)
  (p: P.parser k t)
  (terminator: t)
  (v: Seq.seq LP.byte)
: Lemma
  (ensures (
    P.parse (P.parse_string p terminator) v ==
    LP.parse (LUT.parse_list_up_to (P.cond_string_up_to terminator) p (string_prf p terminator)) v
  ))
= LP.parser_kind_prop_equiv k p

let string_elem (#t: eqtype) (terminator: t) : Type0 =
  LUT.refine_with_cond (LUT.negate_cond (P.cond_string_up_to terminator))

let rec vs_string_aux
  (#d: state_dict) (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (vs: value_spec d t)
  (pos: S.aenv) (l: list (string_elem terminator)) (z: t) (x: forevery_values d)
: GTot (S.vres d) (decreases l)
= match l with
  | [] -> vs pos z x
  | v :: tl -> vres_then (vs pos v x) (fun x1 -> vs_string_aux p terminator vs (S.aenv_adv pos (vsize p v)) tl z x1)

let vs_string
  (#d: state_dict) (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (vs: value_spec d t)
: value_spec d (P.cstring t terminator)
= fun pos v x -> vs_string_aux p terminator vs pos (fst v) (snd v) x

let rec vs_string_aux_pure
  (#d: state_dict) (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (vs: value_spec d t)
  (pos: S.aenv) (l: list (string_elem terminator)) (z: t) (x: forevery_values d)
: Lemma
  (requires (value_spec_pure vs))
  (ensures (vs_string_aux p terminator vs pos l z x == S.VOk x))
  (decreases l)
= match l with
  | [] -> elim_pure vs pos z x
  | v :: tl -> elim_pure vs pos v x; vs_string_aux_pure p terminator vs (S.aenv_adv pos (vsize p v)) tl z x

#push-options "--z3rlimit 32"

let rec vspec_string_fold_eq
  (#d: state_dict) (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (s: S.vspec d) (vs: value_spec d t) (o: PM.ptr) (contents rest: Seq.seq U8.t) (x: forevery_values d)
: Lemma
  (requires (vspec_refines p s vs /\ Seq.length rest <= Seq.length contents))
  (ensures (match LP.parse (LUT.parse_list_up_to (P.cond_string_up_to terminator) p (string_prf p terminator)) rest with
    | Some (lz, _) -> S.vspec_string_fold p terminator s o contents rest x ==
        vs_string_aux p terminator vs ({ S.a_start = Seq.length contents - Seq.length rest; S.a_origin = o }) (fst lz) (snd lz) x
    | None -> S.vspec_string_fold p terminator s o contents rest x == S.VErr))
  (decreases (Seq.length rest))
= LUT.parse_list_up_to_eq (P.cond_string_up_to terminator) p (string_prf p terminator) rest;
  let i = { S.contents = contents; S.rest = rest; S.origin = o } in
  elim_refines p s vs i x;
  match LP.parse p rest with
  | None -> ()
  | Some (v, n) ->
    vsize_eq p rest;
    LP.parser_kind_prop_equiv k p;
    if v = terminator then ()
    else begin
      let rest' = Seq.slice rest n (Seq.length rest) in
      match vs (S.venv i) v x with
      | S.VOk x1 -> vspec_string_fold_eq p terminator s vs o contents rest' x1
      | _ -> ()
    end

#pop-options

let wf_string
  (#d: state_dict) (ha: bool)
  (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (s: S.vspec d) (vs: value_spec d t)
: Lemma
  (requires (vspec_wf ha p s vs))
  (ensures (vspec_wf ha (P.parse_string p terminator) (S.vspec_string ha p terminator s) (vs_string p terminator vs)))
= if ha
  then
    intro_refines (P.parse_string p terminator) (S.vspec_string ha p terminator s) (vs_string p terminator vs) (fun i x ->
      parse_string_eq p terminator i.S.rest;
      vspec_string_fold_eq p terminator s vs i.S.origin i.S.contents i.S.rest x)
  else begin
    intro_pure (vs_string p terminator vs) (fun pos v x -> vs_string_aux_pure p terminator vs pos (fst v) (snd v) x);
    wf_of_parser_pure (P.parse_string p terminator) (vs_string p terminator vs)
  end

let vspec_wf_elim
  (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type0) (p: P.parser k t)
  (s: S.vspec d) (vs: value_spec d t) (i: S.vinput) (x: forevery_values d)
: Lemma
  (requires (vspec_wf ha p s vs /\ vinput_ok i))
  (ensures (match P.parse p i.S.rest with
    | Some (v, _) -> s i x == vs (S.venv i) v x
    | None -> s i x == S.VErr))
= elim_refines p s vs i x
