module LowParse.SLow.Tac.Enum
include LowParse.SLow.Enum

module T = LowParse.TacLib

noextract
let rec enum_tac_gen
  (t_cons_nil: T.term)
  (t_cons: T.term)
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= match e with
  | [] -> T.fail "enum_tac_gen: e must be cons"
  | [_] ->
    T.apply t_cons_nil;
    T.iseq [
      T.solve_vc;
      T.solve_vc;
    ];
    T.qed ()
  | _ :: e_ ->
    T.apply t_cons;
    T.iseq [
      T.solve_vc;
      (fun () -> enum_tac_gen t_cons_nil t_cons e_);
    ];
    T.qed ()

noextract
let maybe_enum_key_of_repr_tac
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= enum_tac_gen (quote maybe_enum_key_of_repr'_t_cons_nil') (quote maybe_enum_key_of_repr'_t_cons') e

noextract
let enum_repr_of_key_tac
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= enum_tac_gen (quote enum_repr_of_key_cons_nil') (quote enum_repr_of_key_cons') e

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
  T.apply fu;
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
  T.apply fu;
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
  T.apply fu;
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
  T.apply fu;
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
  T.apply fu;
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
  T.apply fu;
  T.iseq [
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    T.solve_vc;
    (fun () -> enum_repr_of_key_tac e);
  ]

noextract
let synth_maybe_enum_key_inv_unknown_tac (#key: Type) (x: key) : T.Tac unit =
  let open T in
    destruct (quote x);
    to_all_goals (fun () ->
      let breq = intros_until_squash () in
      rewrite breq;
      norm [delta; iota; zeta; primops];
      trivial ();
      qed ()
    );
    qed ()

noextract
let forall_maybe_enum_key_known_tac () : T.Tac unit =
      let open T in
      norm [delta; iota; zeta; primops];
      trivial ();
      qed ()

noextract
let forall_maybe_enum_key_unknown_tac () : T.Tac unit =
      let open T in
      let x = intro () in
      norm [delta; iota; zeta; primops];
      trivial ();
      qed ()
