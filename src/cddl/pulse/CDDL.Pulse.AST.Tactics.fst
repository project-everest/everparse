module CDDL.Pulse.AST.Tactics
include CDDL.Spec.AST.Elab
include CDDL.Pulse.AST.Bundle

let solve_by_norm () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta; iota; zeta; primops];
  FStar.Tactics.trefl ()

let solve_sem () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_attr [`%sem_attr]; iota; zeta; primops; nbe];
  FStar.Tactics.smt ()

let trefl_or_trivial () : FStar.Tactics.Tac unit =
  FStar.Tactics.first [
    (fun _ -> FStar.Tactics.trefl ());
    (fun _ -> FStar.Tactics.trivial ());
  ]

let trefl_or_norm () : FStar.Tactics.Tac unit =
  FStar.Tactics.first [
    trefl_or_trivial;
    (fun _ -> FStar.Tactics.norm [nbe; delta; iota; zeta; primops]; trefl_or_trivial ());
    (fun _ -> FStar.Tactics.norm [delta; iota; zeta; primops]; trefl_or_trivial ());
  ]

exception ExceptionOutOfFuel

let solve_mk_wf_typ_fuel_for () : FStar.Tactics.Tac unit =
  let rec aux (n: nat) : FStar.Tactics.Tac unit =
    FStar.Tactics.try_with
    (fun _ ->
      FStar.Tactics.print ("solve_mk_wf_typ_fuel_for with fuel " ^ string_of_int n ^ "\n");
      FStar.Tactics.apply (FStar.Tactics.mk_app (`mk_wf_typ_fuel_for_intro) [quote n, FStar.Tactics.Q_Explicit]);
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.try_with
        (fun _ ->
          FStar.Tactics.trefl ()
        )
        (fun e -> 
          let g = FStar.Tactics.cur_goal () in
          FStar.Tactics.print ("solve_mk_wf_typ_fuel_for Failure: " ^ FStar.Tactics.term_to_string g ^ "\n");
          let g0 = quote (squash (ROutOfFuel == RSuccess ())) in
          FStar.Tactics.print ("Comparing with " ^ FStar.Tactics.term_to_string g0 ^ "\n");
          let e' =
            if g `FStar.Tactics.term_eq` g0
            then ExceptionOutOfFuel
            else e
          in
          FStar.Tactics.raise e'
        )
      )
      (fun e ->
        match e with
        | ExceptionOutOfFuel -> aux (n + 1)
        | _ -> FStar.Tactics.raise e
      )
  in
  aux 0

open CDDL.Spec.AST.Driver

[@@base_attr; noextract_to "krml"] noextract
let list_hd (#t: Type) (l: list t { Cons? l }) : Tot t =
  let hd :: _ = l in hd

[@@base_attr; noextract_to "krml"] noextract
let list_tl (#t: Type) (l: list t { Cons? l }) : Tot (list t) =
  let _ :: tl = l in tl

[@@base_attr; noextract_to "krml"] noextract
let pair_fst (#t1 #t2: Type) (x: (t1 & t2)) : Tot t1 =
  let (x1, _) = x in x1

[@@base_attr; noextract_to "krml"] noextract
let pair_snd (#t1 #t2: Type) (x: (t1 & t2)) : Tot t2 =
  let (_, x2) = x in x2

[@@base_attr; noextract_to "krml"] noextract
let pull_name
  (l: list (string & decl) { Cons? l })
: Tot string
= (pair_fst (list_hd l))

[@@base_attr; noextract_to "krml"] noextract
let pull_type
  (l: list (string & decl) { Cons? l /\ DType? (snd (List.Tot.hd l)) })
: Tot typ
= (DType?._0 (pair_snd (list_hd l)))

[@@base_attr; noextract_to "krml"] noextract
let pull_group
  (l: list (string & decl) { Cons? l /\ DGroup? (snd (List.Tot.hd l)) })
: Tot group
= (DGroup?._0 (pair_snd (list_hd l)))

noextract [@@noextract_to "krml"]
let base_steps = [
      zeta; iota; primops;
  ]

noextract [@@noextract_to "krml"]
let base_delta_only_steps = [
        `%List.Tot.for_all;
        `%List.Tot.length;
        `%FStar.Int.Cast.uint32_to_uint8;
        `%pow2;
        `%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2;
        `%fst; `%snd; `%Mktuple2?._1; `%Mktuple2?._2;
        `%Some?; `%None?;
        `%Some?.v;
]

noextract [@@noextract_to "krml"]
let steps =
      delta_attr [`%base_attr; `%sem_attr] ::
      delta_only (
        `%Mkbundle_env?.be_v ::
        base_delta_only_steps
      ) ::
      base_steps

let bundle_get_impl_type_steps =
  delta_attr [
    `%base_attr;
    `%bundle_attr;
    `%bundle_get_impl_type_attr;
  ] ::
  delta_only (
    `%Mkbundle?.b_impl_type ::
    `%Mkarray_bundle?.ab_impl_type ::
    `%Mkmap_bundle?.mb_impl_type ::
    base_delta_only_steps
  ) ::
  base_steps

let bundle_get_spec_type_steps =
  delta_attr [
    `%base_attr;
    `%bundle_attr;
    `%bundle_get_impl_type_attr;
  ] ::
  delta_only (
    `%Mkbundle?.b_spec_type ::
    `%Mkarray_bundle?.ab_spec_type ::
    `%Mkmap_bundle?.mb_spec_type ::
    base_delta_only_steps
  ) ::
  base_steps

let bundle_get_rel_steps =
  delta_attr [
    `%base_attr;
    `%bundle_attr;
    `%bundle_get_impl_type_attr;
  ] ::
  delta_only (
    `%Mkbundle?.b_spec_type ::
    `%Mkarray_bundle?.ab_spec_type ::
    `%Mkmap_bundle?.mb_spec_type ::
    `%Mkbundle?.b_impl_type ::
    `%Mkarray_bundle?.ab_impl_type ::
    `%Mkmap_bundle?.mb_impl_type ::
    `%Mkbundle?.b_rel ::
    `%Mkarray_bundle?.ab_rel ::
    `%Mkmap_bundle?.mb_rel ::
    base_delta_only_steps
  ) ::
  base_steps

let bundle_steps = 
  delta_attr [
    `%base_attr;
    `%bundle_attr;
    `%sem_attr; // because there are validators in the middle of bundles
  ] ::
  delta_only (
    `%Mkbundle_env?.be_v ::
    base_delta_only_steps
  ) ::
  base_steps

[@@noextract_to "krml"; sem_attr] noextract inline_for_extraction
let inline_coerce_eq (#[@@@erasable] a:Type) (#[@@@erasable]b:Type) ([@@@erasable] peq:squash (a == b)) (x:a) : b = x

[@@noextract_to "krml"; sem_attr] noextract inline_for_extraction
let inline_coerce_eq_reverse (#a:Type) (#b:Type) (_:squash (b == a)) (x:a) : b = x

