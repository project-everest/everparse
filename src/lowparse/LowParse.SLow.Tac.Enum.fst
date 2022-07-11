module LowParse.SLow.Tac.Enum
include LowParse.Spec.Tac.Enum
include LowParse.SLow.Enum

module T = LowParse.TacLib

//
// The enum tactic solves goals of type ?u:eqtype with enum types that are
//   in the environment at type Type0
// So typechecking such uvars fails since F* 2635 bug fix
//   (since uvar solutions are checked with smt off)
//
// To circumvent that, we use t_apply with tc_resolve_uvars flag on,
//   so that ?u will be typechecked as soon as it is resolved,
//   resulting in an smt guard that will be added to the proofstate
//

let apply (t:T.term) : T.Tac unit =
  T.t_apply true false true t

noextract
let parse32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let fu = quote (parse32_maybe_enum_key_gen #k #key #repr #p p32 e) in
  apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> maybe_enum_key_of_repr_tac #key #repr e);
  ]

noextract
let parse32_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
  ()
: T.Tac unit
= T.tassert (Cons? e);
  let fu = quote (parse32_enum_key_gen #k #key #repr p e) in
  apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> parse32_maybe_enum_key_tac p32 e ())
  ]

noextract
let serialize32_enum_key_gen_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let fu = quote (serialize32_enum_key_gen #k #key #repr #p #s s32 e) in
  apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> enum_repr_of_key_tac e);
  ]

noextract
let serialize32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let fu = quote (serialize32_maybe_enum_key_gen #k #key #repr #p #s s32 e) in
  apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> enum_repr_of_key_tac e);
  ]

noextract
let size32_enum_key_gen_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let fu = quote (size32_enum_key_gen #k #key #repr #p #s s32 e) in
  apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> enum_repr_of_key_tac e);
  ]

noextract
let size32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let fu = quote (size32_maybe_enum_key_gen #k #key #repr #p #s s32 e) in
  apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> enum_repr_of_key_tac e);
  ]
