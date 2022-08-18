module Test

open Steel.ST.GenElim

module A = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt
module R = Steel.ST.Reference

open LowParse.SteelST.Int
open LowParse.SteelST.BoundedInt
open LowParse.SteelST.VLData
open LowParse.SteelST.List

module U16 = FStar.UInt16
module U32 = FStar.UInt32

module F = LowParse.SteelST.Fold
module Printf_dummy = LowStar.Printf // for dependencies only

#set-options "--ide_id_info_off"

let test_accessor
  (#vb: v _ _)
  (b: byte_array)
: STT U16.t
    (aparse (parse_u16 `nondep_then` parse_u16) b vb)
    (fun r -> aparse (parse_u16 `nondep_then` parse_u16) b vb `star`
      pure (U16.v r == U16.v (fst vb.contents) \/ U16.v r == U16.v (snd vb.contents)))
= with_pair_fst _ _ b (fun bf ->
    with_pair_snd jump_u16 _ b (fun bs ->
      let f = read_u16 bf in
      let s = read_u16 bs in
      let res = 
        if f `U16.lt` s
        then s
        else f
      in
      noop ();
      return res
  ))

let test_prog_1 = F.run_prog
  (F.impl_bind
    _
    (F.impl_u8 (F.initial_ser_index F.TU8))
    _
    (fun w ->
      F.impl_action
        _
        (F.impl_ser_u8 w ())
        _
    )
  )

let test_prog_2 = F.run_prog
      (F.impl_bind
        _
        (F.impl_action _ (F.impl_ser_u8 #_ #(F.initial_ser_index F.TU8) 42uy ()) _)
        _
        (fun _ -> F.impl_list
          _
          (F.impl_ret #_ #_ #_ #F.TU8 ())
          (jump_weaken F.pkind (jump_constant_size parse_u8  SZ.one_size) ())
          (F.with_context_arrays_ptr_nil F.TU8)
          (F.load_context_arrays_ptr_nil F.TU8)
          (F.store_context_arrays_ptr_nil F.TU8)
        )
      )

module P = LowParse.SteelST.Fold.Print
module G = LowParse.SteelST.Fold.Gen

noextract
[@@G.specialize]
let test_print_u8 : G.prog P.state_t P.action_t _ unit () () =
  G.PBind
    (G.PU8 ())
    (fun x -> G.PBind
      (G.PAction (P.PrintString "uint8:"))
      (fun _ -> G.PBind
        (G.PAction (P.PrintU8 x))
        (fun _ -> G.PAction (P.PrintString ";"))
      )
    )

noextract
[@@G.specialize]
let pchoice
  (#state_i: Type)
  (#state_t: state_i -> Type)
  (#action_t: (ret_t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (#ttrue: G.typ)
  (ptrue: G.prog state_t action_t ttrue ret_t pre post)
  (#tfalse: G.typ)
  (pfalse: G.prog state_t action_t tfalse ret_t pre post)
: Tot (G.prog state_t action_t (G.TChoice (fun b -> if b then ttrue else tfalse)) ret_t pre post)
= G.PChoice
    (fun b -> G.PIf #_ #_ #_ #(if b then ttrue else tfalse) b (fun _ -> ptrue) (fun _ -> pfalse))

noextract
[@@G.specialize]
let test_print_choice
  (#ttrue: G.typ)
  (ptrue: G.prog P.state_t P.action_t ttrue unit () ())
  (#tfalse: G.typ)
  (pfalse: G.prog P.state_t P.action_t tfalse unit () ())
: Tot (G.prog P.state_t P.action_t (G.TChoice (fun b -> if b then ttrue else tfalse)) unit () ())
= G.PBind
    (G.PAction (P.PrintString "choice:"))
    (fun _ -> pchoice
      (G.PBind
        (G.PAction (P.PrintString "true{"))
        (fun _ -> G.PBind
          ptrue
          (fun _ -> G.PAction (P.PrintString "};"))
        )
      )
      (G.PBind
        (G.PAction (P.PrintString "false{"))
        (fun _ -> G.PBind
          pfalse
          (fun _ -> G.PAction (P.PrintString "};"))
        )
      )
    )

noextract
[@@G.specialize]
let test_print_list
  (#t: G.typ)
  (p: G.prog P.state_t P.action_t t unit () ())
: Tot (G.prog P.state_t P.action_t (G.TList t) unit () ())
= G.PBind
    (G.PAction (P.PrintString "list:["))
    (fun _ -> G.PBind
      (G.PList () p)
      (fun _ -> G.PAction (P.PrintString "];"))
    )

noextract
[@@G.specialize]
let prog_test_pretty_print : G.prog P.state_t P.action_t _ unit () () =
  G.PPair
    test_print_u8
    (fun _ ->
      test_print_choice
        (test_print_list test_print_u8)
        test_print_u8
    )

module T = FStar.Tactics

inline_for_extraction
noextract
[@@T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
let specialize_impl_test_pretty_print : G.fold_impl_t _ _ (G.sem P.action_sem prog_test_pretty_print) = G.impl P.a_cl P.ptr_cl prog_test_pretty_print

let test_pretty_print =
  G.extract_impl_fold
    specialize_impl_test_pretty_print
    P.mk_ll_state

inline_for_extraction noextract
let u16_max (x1 x2: U16.t) : Tot U16.t
= if x1 `U16.lte` x2 then x2 else x1

[@@__reduce__]
let p = parse_vldata 1 (parse_list parse_u16)

let q = p

// let validate_p : validator q = validate_vldata_gen 1 (unconstrained_bounded_integer 1) (fun _ -> true) (validate_list_total_constant_size parse_u16 (SZ.mk_size_t 2ul))
let validate_p : validator q = validate_vldata_gen 1 (unconstrained_bounded_integer 1) (fun _ -> true) (validate_list validate_u16)

let state (_: U16.t) (_: list U16.t) : Tot vprop = emp

inline_for_extraction
noextract
let iter_max
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t)
: ST U16.t
    (aparse (parse_list parse_u16) a va)
    (fun _ -> aparse (parse_list parse_u16) a va)
    (SZ.size_v len == A.length (array_of' va))
    (fun _ -> True)
=
    rewrite emp (state _ _);
    let res = list_iter jump_u16 u16_max state
      (fun va a accu l ->
        rewrite (state _ _) emp;
        let wa = read_u16 a in
        let res = u16_max accu wa in
        rewrite emp (state _ _);
        return res
      )
      a len 0us
    in
    rewrite (state _ _) emp;
    return res

#push-options "--z3rlimit 128"

let test (a: byte_array) (#va: _) (len: SZ.size_t) (perr: R.ref U32.t)
: ST U16.t
  (A.arrayptr a va `star` exists_ (fun v -> R.pts_to perr full_perm v))
  (fun _ -> A.arrayptr a va `star` exists_ (fun v -> R.pts_to perr full_perm v))
  (SZ.size_v len == A.length (A.array_of va))
  (fun _ -> True)
= let _ = gen_elim () in
  R.write perr 0ul;
  let sz = validate_p a len perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err = 0ul
  then begin
    let ar = peek_strong_with_size p a sz in
    let _ = gen_elim () in
    let gac = ghost_elim_vldata_gen _ _ _ a in
    let _ = gen_elim () in
    let acsz = read_bounded_integer _ a in
    let ac = hop_aparse_aparse (jump_bounded_integer 1) _ a gac in
    let res = iter_max ac (SZ.mk_size_t acsz) in
    let _ = intro_vldata_gen _ _ _ a ac in
    let va' = elim_aparse p a in
    parse_injective p (Seq.slice (A.contents_of' va) 0 (SZ.size_v sz)) (A.contents_of' va');
    Seq.lemma_split (A.contents_of' va) (SZ.size_v sz);
    let _ = A.join a ar in
    return res
  end
  else begin
    noop ();
    return 0us
  end

#pop-options

let main () = C.EXIT_SUCCESS
