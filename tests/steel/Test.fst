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

module Printf_dummy = LowStar.Printf // for dependencies only

#set-options "--ide_id_info_off"

let test_accessor
  (#vb: v _ _)
  (b: byte_array)
: STT U16.t
    (aparse (parse_u16 `nondep_then` parse_u16) b vb)
    (fun r -> aparse (parse_u16 `nondep_then` parse_u16) b vb `star`
      pure (U16.v r == U16.v (fstp vb.contents) \/ U16.v r == U16.v (sndp vb.contents)))
= with_pair_fst parse_u16 parse_u16 b (fun bf ->
    with_pair_snd jump_u16 parse_u16 b (fun bs ->
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

let parse_bool : parser (parse_filter_kind parse_u8_kind) bool =
  parse_u8
    `parse_filter`
    (fun x -> (x = 1uy || x = 0uy))
    `parse_synth`
    (fun x -> (x = 1uy))

let serialize_bool : serializer parse_bool =
  serialize_synth
    (parse_u8 `parse_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    (serialize_u8 `serialize_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun y -> if y then 1uy else 0uy)
    ()

inline_for_extraction
noextract
let validate_bool : validator parse_bool =
  validate_synth
    (validate_filter
      validate_u8
      read_u8
      (fun x -> (x = 1uy || x = 0uy))
      (fun x -> (x = 1uy || x = 0uy))
    )
    (fun x -> (x = 1uy))
    ()

inline_for_extraction
noextract
let read_bool : leaf_reader parse_bool =
  read_synth'
    (read_filter read_u8 (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    ()

inline_for_extraction
noextract
let write_bool: exact_writer serialize_bool =
  exact_write_synth'
    (exact_write_filter
      write_u8
      (fun x -> (x = 1uy || x = 0uy))
    )
    (fun x -> (x = 1uy))
    (fun y -> if y then 1uy else 0uy)
    ()

module P = LowParse.SteelST.Fold.Print
module G = LowParse.SteelST.Fold.Gen

[@@G.specialize; noextract_to "krml"]
type scalar_t = | U8 | U32 | Bool

[@@G.specialize; noextract_to "krml"]
inline_for_extraction
let type_of_scalar (s: scalar_t) : Tot Type =
  match s with
  | U8 -> FStar.UInt8.t
  | U32 -> FStar.UInt32.t
  | Bool -> bool

[@@G.specialize; noextract_to "krml"]
let p_of_s (s: scalar_t) : G.scalar_ops (type_of_scalar s) =
  match s with
  | U8 -> {
           G.scalar_parser = weaken G.pkind parse_u8;
           G.scalar_validator = validate_weaken _ validate_u8 ();
           G.scalar_reader = read_weaken _ read_u8;
           G.scalar_jumper = jump_weaken _ jump_u8 ();
         }
  | U32 -> {
           G.scalar_parser = weaken G.pkind parse_u32;
           G.scalar_validator = validate_weaken _ validate_u32 ();
           G.scalar_reader = read_weaken _ read_u32;
           G.scalar_jumper = jump_weaken _ jump_u32 ();
         }
  | Bool -> {
           G.scalar_parser = weaken G.pkind parse_bool;
           G.scalar_validator = validate_weaken _ validate_bool ();
           G.scalar_reader = read_weaken _ read_bool;
           G.scalar_jumper = jump_weaken _ (jump_constant_size parse_bool SZ.one_size) ();
         }

noextract
[@@G.specialize]
let test_print_u8 : G.prog type_of_scalar P.state_t P.action_t _ unit () () =
  G.PBind
    (G.PScalar () U8)
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
  (#ttrue: G.typ type_of_scalar)
  (ptrue: G.prog type_of_scalar state_t action_t ttrue ret_t pre post)
  (#tfalse: G.typ type_of_scalar)
  (pfalse: G.prog type_of_scalar state_t action_t tfalse ret_t pre post)
: Tot (G.prog type_of_scalar state_t action_t (G.TChoice Bool (fun b -> G.TIf b (fun _ -> ttrue) (fun _ -> tfalse))) ret_t pre post)
= G.PChoice
    (fun b -> G.PIfT b (fun _ -> ptrue) (fun _ -> pfalse))

noextract
[@@G.specialize]
let test_print_choice
  (#ttrue: G.typ type_of_scalar)
  (ptrue: G.prog type_of_scalar P.state_t P.action_t ttrue unit () ())
  (#tfalse: G.typ type_of_scalar)
  (pfalse: G.prog type_of_scalar P.state_t P.action_t tfalse unit () ())
: Tot (G.prog type_of_scalar P.state_t P.action_t (G.TChoice Bool (fun b -> G.TIf b (fun _ -> ttrue) (fun _ -> tfalse))) unit () ())
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
  (#t: G.typ type_of_scalar)
  (p: G.prog type_of_scalar P.state_t P.action_t t unit () ())
: Tot (G.prog type_of_scalar P.state_t P.action_t (G.TList U32 SZ.mk_size_t t) unit () ())
= G.PBind
    (G.PAction (P.PrintString "list:["))
    (fun _ -> G.PBind
      (G.PList U32 SZ.mk_size_t _ p)
      (fun _ -> G.PAction (P.PrintString "];"))
    )

noextract
[@@G.specialize]
let prog_test_pretty_print : G.prog type_of_scalar P.state_t P.action_t _ unit () () =
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
let specialize_impl_test_pretty_print0 =
  G.impl p_of_s P.a_cl P.ptr_cl prog_test_pretty_print

noextract
let typ_of_test_pretty_print =
  G.typ_of_prog prog_test_pretty_print

noextract
let type_of_test_pretty_print =
  G.type_of_typ (G.typ_of_prog prog_test_pretty_print)

noextract
let parser_of_test_pretty_print : parser G.pkind type_of_test_pretty_print =
  G.parser_of_typ p_of_s (G.typ_of_prog prog_test_pretty_print)

noextract
let sem_of_test_pretty_print : G.fold_t P.state_t type_of_test_pretty_print unit () () =
  G.sem P.action_sem prog_test_pretty_print

inline_for_extraction
noextract
let specialize_impl_test_pretty_print : G.fold_impl_t P.cl parser_of_test_pretty_print sem_of_test_pretty_print =
  specialize_impl_test_pretty_print0

let test_pretty_print =
  G.extract_impl_fold_no_failure
    P.no_fail
    specialize_impl_test_pretty_print
    P.mk_ll_state

[@@T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
inline_for_extraction
noextract
let validate_test_pretty_print0 =
  G.validator_of_typ p_of_s (G.typ_of_prog prog_test_pretty_print)

let validate_test_pretty_print : validator parser_of_test_pretty_print =
  validate_test_pretty_print0

#push-options "--z3rlimit 64"
#restart-solver

let full_test_pretty_print
  (#vb: A.v byte)
  (b: byte_array)
  (len: SZ.size_t)
: ST unit (A.arrayptr b vb) (fun _ -> A.arrayptr b vb)
    (A.length (A.array_of vb) == SZ.size_v len)
    (fun _ -> True)
= with_local 0ul (fun perr ->
    let sz = validate_test_pretty_print b len perr in
    let _ = gen_elim () in
    let err = read_replace perr in
    if err = 0ul
    then begin
      let _ = ghost_peek_strong parser_of_test_pretty_print b in
      let _ = gen_elim () in
      let _ = test_pretty_print _ b () in
      let _ = gen_elim () in
      rewrite (P.cl.ll_state_match _ _) emp;
      unpeek_strong b _ _
    end else begin
      Steel.ST.Printf.print_string "invalid data"
    end
  )

#pop-options

module W = LowParse.SteelST.Fold.SerializationState

noextract
[@@G.specialize]
let test_write1 : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
= G.PBind
    (G.PScalar _ U32)
    (fun v1 -> G.PBind
      (G.PAction (W.AWrite _ U32 v1))
      (fun _ -> G.PAction (W.AWeaken _ (W.index_with_trivial_postcond [W.IParseValue (G.TScalar U32)]) ()))
    )

// FIXME: WHY WHY WHY do I need those i0, i1, etc. annotations to typecheck this program? Without them, F* will blow up, increasing memory consumption and not returning
noextract
[@@G.specialize]
let test_write2 : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
= let i0 = W.initial_index type_of_scalar in
  G.PPair
    (G.PScalar i0 U32)
    (fun v1 -> G.PBind
      (G.PScalar i0 U32)
      (fun v2 -> 
        let i1 = W.i_nil i0 (G.TScalar U32) in
        G.PBind
        (G.PAction (W.ANil i0 (G.TScalar U32)))
        (fun _ -> 
        let i2 = W.i_write i1 U32 v2 in
        G.PBind
          (G.PAction (W.AWrite i1 U32 v2))
          (fun _ -> 
            let i3 = W.i_cons i2 (G.TScalar U32) () in
            G.PBind
            (G.PAction (W.ACons i2 (G.TScalar U32) ()))
            (fun _ -> 
              let i4 = W.i_write i3 U32 v1 in
              G.PBind
              (G.PAction (W.AWrite i3 U32 v1))
              (fun _ -> 
                let i5 = W.i_cons i4 (G.TScalar U32) () in
                G.PBind
                (G.PAction (W.ACons i4 (G.TScalar U32) ()))
                (fun _ -> 
                  let i6 = W.i_list i5 U32 SZ.mk_size_t (G.TScalar U32) () in
                  G.PBind
                  (G.PAction
                    (W.AList i5
                      U32 SZ.mk_size_t
                      (fun x -> x `SZ.size_le` SZ.mk_size_t 4294967295ul)
                      (fun x -> SZ.to_u32 x)
                      (G.TScalar U32)
                      ()
                  ))
                  (fun _ -> G.PAction (W.AWeaken i6 (W.index_with_trivial_postcond [W.IParseValue (G.TList U32 SZ.mk_size_t (G.TScalar U32))]) ()))
                )
              )
            )
          )
        )
      )
    )

noextract
[@@G.specialize]
let test_write3 : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
=
  let i0 = W.initial_index type_of_scalar in
  G.PPair
    (G.PScalar i0 U32)
    (fun v1 -> G.PBind
      (G.PScalar i0 U32)
      (fun v2 -> 
        G.pbind
        (G.PAction (W.ANil i0 (G.TScalar U32)))
        (fun (i1: W.state_i type_of_scalar) _ _ -> 
        G.pbind
          (G.PAction (W.AWrite i1 U32 v2))
          (fun (i2: W.state_i type_of_scalar) _ _ -> 
            G.pbind
            (G.PAction (W.ACons i2 (G.TScalar U32) ()))
            (fun (i3: W.state_i type_of_scalar) _ _ -> 
              G.pbind
              (G.PAction (W.AWrite i3 U32 v1))
              (fun (i4: W.state_i type_of_scalar) _ _ -> 
                G.pbind
                (G.PAction (W.ACons i4 (G.TScalar U32) ()))
                (fun (i5: W.state_i type_of_scalar) _ _ -> 
                  G.pbind
                  (G.PAction
                    (W.AList i5
                      U32 SZ.mk_size_t
                      (fun x -> x `SZ.size_le` SZ.mk_size_t 4294967295ul)
                      (fun x -> SZ.to_u32 x)
                      (G.TScalar U32)
                      ()
                  ))
                  (fun (i6: W.state_i type_of_scalar) _ _ -> G.PAction (W.AWeaken i6 (W.index_with_trivial_postcond [W.IParseValue (G.TList U32 SZ.mk_size_t (G.TScalar U32))]) ()))
                )
              )
            )
          )
        )
      )
    )

[@@G.specialize]
noextract
let w_of_s
  (s: scalar_t)
: Tot (W.r_to_l_write_t (p_of_s s).scalar_parser)
= match s with
  | U8 -> coerce _ (W.r_to_l_write_rewrite (W.r_to_l_write_constant_size write_u8 SZ.one_size) (p_of_s s).scalar_parser)
  | U32 -> coerce _ (W.r_to_l_write_rewrite (W.r_to_l_write_constant_size write_u32 (SZ.mk_size_t 4ul)) (p_of_s s).scalar_parser)
  | Bool -> coerce _ (W.r_to_l_write_rewrite (W.r_to_l_write_constant_size write_bool SZ.one_size) (p_of_s s).scalar_parser)

inline_for_extraction noextract
[@@T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
let specialize_test_write3 b b_sz a =
  G.impl p_of_s (W.a_cl p_of_s w_of_s b b_sz a) (W.ptr_cl p_of_s b b_sz a) test_write3

let extract_test_write3 vb b b_sz =
  G.extract_impl_fold_unit
    (specialize_test_write3 b b_sz (A.array_of vb))
    (W.mk_initial_state p_of_s vb b b_sz)

noextract
[@@G.specialize]
let tif = G.TIf #_ #type_of_scalar

noextract
[@@G.specialize]
let tchoice = G.TChoice #_ #type_of_scalar

noextract
[@@G.specialize]
let test_write4_if_true
  (b: bool)
  (sq: squash (b == true))
: Tot (G.typ type_of_scalar)
= G.TList U32 SZ.mk_size_t (G.TScalar U8)

noextract
[@@G.specialize]
let test_write4_if_false
  (b: bool)
  (sq: squash (b == false))
: Tot (G.typ type_of_scalar)
= G.TScalar U8

noextract
[@@G.specialize]
let test_write4_choice_payload
  (b: bool)
: Tot (G.typ type_of_scalar)
= tif b (test_write4_if_true b) (test_write4_if_false b)

// #push-options "--debug Test --debug_level Norm"

#push-options "--z3rlimit 16"
#restart-solver

noextract
[@@G.specialize;
  T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
let test_write4 : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
=
  let i0 = W.initial_index type_of_scalar in
  G.PBind
    (G.PScalar i0 U32) // dummy read, I am only testing actions here
    (fun _ -> G.pbind
      (G.PAction (W.ANil i0 (G.TScalar U8)))
      (fun (i1: W.state_i type_of_scalar) _ _ -> G.pbind
        (G.PAction (W.AWrite i1 U8 104uy))
        (fun (i2: W.state_i type_of_scalar) _ _ -> G.pbind
          (G.PAction (W.ACons i2 (G.TScalar U8) ()))
          (fun (i3: W.state_i type_of_scalar) _ _ -> G.pbind
            (G.PAction (W.AWrite i3 U8 117uy))
            (fun (i4: W.state_i type_of_scalar) _ _ -> G.pbind
              (G.PAction (W.ACons i4 (G.TScalar U8) ()))
              (fun (i5: W.state_i type_of_scalar) _ _ -> G.pbind
                (G.PAction (W.AWrite i5 U8 98uy))
                (fun (i6: W.state_i type_of_scalar) _ _ -> G.pbind
                  (G.PAction (W.ACons i6 (G.TScalar U8) ()))
                  (fun (i7: W.state_i type_of_scalar) _ _ -> G.pbind
                    (G.PAction (W.AList i7
                      U32 SZ.mk_size_t
                      (fun x -> x `SZ.size_le` SZ.mk_size_t 4294967295ul)
                      (fun x -> SZ.to_u32 x)
                      (G.TScalar U8)
                      ()
                    ))
                    (fun (i8: W.state_i type_of_scalar) _ _ -> G.pbind
                      (G.PAction (W.AIf i8
                        (G.TList U32 SZ.mk_size_t (G.TScalar U8))
                        true
                        (test_write4_if_true true)
                        (test_write4_if_false true)
                        ()
                      ))
                      (fun (i9: W.state_i type_of_scalar) _ _ -> G.pbind
                        (G.PAction (W.AWrite i9 Bool true))
                        (fun (i10: W.state_i type_of_scalar) _ _ -> G.pbind
                          (G.PAction (
                            W.AChoice i10
                            Bool
                            (tif true
                              (test_write4_if_true true)
                              (test_write4_if_false true)
                            )
                            test_write4_choice_payload
                            ()
                          ))
                          (fun (i11: W.state_i type_of_scalar) _ _ -> G.pbind
                            (G.PAction (W.AWrite i11 U8 70uy))
                            (fun (i12: W.state_i type_of_scalar) _ _ -> G.pbind
                              (G.PAction (W.APair i12
                                (G.TScalar U8)
                                (tchoice Bool test_write4_choice_payload)
                                ()
                              ))
                              (fun (i13: W.state_i type_of_scalar) _ _ ->
                                G.PAction (W.AWeaken i13
                                  (W.index_with_trivial_postcond [W.IParseValue
                                    (G.TPair
                                      (G.TScalar U8)
                                      (tchoice Bool test_write4_choice_payload)
                                    )
                                  ])
                                  ()
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

#pop-options

[@@normalize_for_extraction [delta_attr [`%G.specialize]; iota; zeta; primops]]
let extract_test_write4 vb b b_sz =
  G.extract_impl_fold_unit
    (G.impl p_of_s (W.a_cl p_of_s w_of_s b b_sz (A.array_of vb)) (W.ptr_cl p_of_s b b_sz (A.array_of vb)) test_write4)
    (W.mk_initial_state p_of_s vb b b_sz)

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

#push-options "--z3rlimit 64"
#restart-solver

let test (a: byte_array) (#va: _) (len: SZ.size_t)
: ST U16.t
  (A.arrayptr a va)
  (fun _ -> A.arrayptr a va)
  (SZ.size_v len == A.length (A.array_of va))
  (fun _ -> True)
= with_local 0ul (fun perr ->
  let sz = validate_p a len perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err = 0ul
  then begin
    let ar = ghost_peek_strong p a in
    let _ = gen_elim () in
    let gac = ghost_elim_vldata_gen _ _ _ a in
    let _ = gen_elim () in
    let acsz = read_bounded_integer _ a in
    let ac = hop_aparse_aparse (jump_bounded_integer 1) _ a gac in
    let res = iter_max ac (SZ.mk_size_t acsz) in
    let _ = intro_vldata_gen 1 (unconstrained_bounded_integer 1) _ a ac in
    unpeek_strong a va ar;
    return res
  end
  else begin
    noop ();
    return 0us
  end
  )

#pop-options
