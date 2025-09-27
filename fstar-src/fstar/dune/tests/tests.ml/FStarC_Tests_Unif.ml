open Fstarcompiler
open Prims
let (tcenv : unit -> FStarC_TypeChecker_Env.env) =
  fun uu___ -> FStarC_Tests_Pars.init ()
let (guard_to_string :
  FStarC_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g ->
    match g with
    | FStarC_TypeChecker_Common.Trivial -> "trivial"
    | FStarC_TypeChecker_Common.NonTrivial f ->
        let uu___ = tcenv () in
        FStarC_TypeChecker_Normalize.term_to_string uu___ f
let (success : Prims.bool FStarC_Effect.ref) = FStarC_Effect.mk_ref true
let (fail : Prims.string -> unit) =
  fun msg ->
    FStarC_Format.print_string msg;
    FStarC_Effect.op_Colon_Equals success false
let (guard_eq :
  Prims.int ->
    FStarC_TypeChecker_Common.guard_formula ->
      FStarC_TypeChecker_Common.guard_formula -> unit)
  =
  fun i ->
    fun g ->
      fun g' ->
        let uu___ =
          match (g, g') with
          | (FStarC_TypeChecker_Common.Trivial,
             FStarC_TypeChecker_Common.Trivial) -> (true, g, g')
          | (FStarC_TypeChecker_Common.NonTrivial f,
             FStarC_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu___1 = tcenv () in
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.EraseUniverses] uu___1 f in
              let f'1 =
                let uu___1 = tcenv () in
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.EraseUniverses] uu___1 f' in
              let uu___1 = FStarC_Tests_Util.term_eq f1 f'1 in
              (uu___1, (FStarC_TypeChecker_Common.NonTrivial f1),
                (FStarC_TypeChecker_Common.NonTrivial f'1))
          | uu___1 -> (false, g, g') in
        match uu___ with
        | (b, g1, g'1) ->
            (if Prims.op_Negation b
             then
               (let uu___2 =
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                  let uu___4 = guard_to_string g'1 in
                  let uu___5 = guard_to_string g1 in
                  FStarC_Format.fmt3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu___3 uu___4 uu___5 in
                fail uu___2)
             else ();
             (let uu___2 = (FStarC_Effect.op_Bang success) && b in
              FStarC_Effect.op_Colon_Equals success uu___2))
let (unify :
  Prims.int ->
    FStarC_Syntax_Syntax.bv Prims.list ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit)
  =
  fun i ->
    fun bvs ->
      fun x ->
        fun y ->
          fun g' ->
            fun check ->
              (let uu___1 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
               FStarC_Format.print1 "%s ..." uu___1);
              (let uu___2 = FStarC_Options.parse_cmd_line () in ());
              (let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term x in
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term y in
               FStarC_Format.print2 "Unify %s\nand %s\n" uu___3 uu___4);
              (let tcenv1 = tcenv () in
               let tcenv2 = FStarC_TypeChecker_Env.push_bvs tcenv1 bvs in
               let g =
                 let uu___3 =
                   let uu___4 = FStarC_TypeChecker_Rel.teq tcenv2 x y in
                   FStarC_TypeChecker_Rel.solve_deferred_constraints tcenv2
                     uu___4 in
                 FStarC_TypeChecker_Rel.simplify_guard tcenv2 uu___3 in
               guard_eq i g.FStarC_TypeChecker_Common.guard_f g';
               check ();
               FStarC_Options.init ())
let (should_fail :
  FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit) =
  fun x ->
    fun y ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let g =
                 let uu___1 = tcenv () in
                 let uu___2 =
                   let uu___3 = tcenv () in
                   FStarC_TypeChecker_Rel.teq uu___3 x y in
                 FStarC_TypeChecker_Rel.solve_deferred_constraints uu___1
                   uu___2 in
               (match g.FStarC_TypeChecker_Common.guard_f with
                | FStarC_TypeChecker_Common.Trivial ->
                    let uu___1 =
                      let uu___2 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term x in
                      let uu___3 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term y in
                      FStarC_Format.fmt2
                        "%s and %s should not be unifiable\n" uu___2 uu___3 in
                    fail uu___1
                | FStarC_TypeChecker_Common.NonTrivial f ->
                    let uu___1 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term x in
                    let uu___2 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term y in
                    let uu___3 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term f in
                    FStarC_Format.print3 "%s and %s are unifiable if %s\n"
                      uu___1 uu___2 uu___3)) ()
      with
      | FStarC_Errors.Error (e, msg, r, _ctx) ->
          let uu___1 = FStarC_Errors_Msg.rendermsg msg in
          FStarC_Format.print1 "Expected failure OK: %s\n" uu___1
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x ->
    fun y ->
      let x1 = FStarC_Tests_Pars.pars x in
      let y1 = FStarC_Tests_Pars.pars y in
      let g =
        let uu___ = tcenv () in
        let uu___1 =
          let uu___2 = tcenv () in FStarC_TypeChecker_Rel.teq uu___2 x1 y1 in
        FStarC_TypeChecker_Rel.solve_deferred_constraints uu___ uu___1 in
      let uu___ = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term x1 in
      let uu___1 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term y1 in
      let uu___2 = guard_to_string g.FStarC_TypeChecker_Common.guard_f in
      FStarC_Format.print3 "%s and %s are unifiable with guard %s\n" uu___
        uu___1 uu___2
let (norm : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ = tcenv () in FStarC_TypeChecker_Normalize.normalize [] uu___ t
let (check_core :
  Prims.int ->
    Prims.bool ->
      Prims.bool ->
        FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit)
  =
  fun i ->
    fun subtyping ->
      fun guard_ok ->
        fun x ->
          fun y ->
            (let uu___1 = FStarC_Options.parse_cmd_line () in ());
            (let env = tcenv () in
             let res =
               if subtyping
               then
                 FStarC_TypeChecker_Core.check_term_subtyping true true env x
                   y
               else
                 FStarC_TypeChecker_Core.check_term_equality true true env x
                   y in
             (match res with
              | Fstarcompiler.FStar_Pervasives.Inl
                  (FStar_Pervasives_Native.None) ->
                  let uu___2 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                  FStarC_Format.print1 "%s core check ok\n" uu___2
              | Fstarcompiler.FStar_Pervasives.Inl
                  (FStar_Pervasives_Native.Some g) ->
                  ((let uu___3 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                    let uu___4 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term g in
                    FStarC_Format.print2
                      "%s core check computed guard %s ok\n" uu___3 uu___4);
                   if Prims.op_Negation guard_ok
                   then FStarC_Effect.op_Colon_Equals success false
                   else ())
              | Fstarcompiler.FStar_Pervasives.Inr err ->
                  (FStarC_Effect.op_Colon_Equals success false;
                   (let uu___3 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                    let uu___4 = FStarC_TypeChecker_Core.print_error err in
                    FStarC_Format.print2 "%s failed\n%s\n" uu___3 uu___4)));
             FStarC_Options.init ())
let (check_core_typing :
  Prims.int -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.typ -> unit)
  =
  fun i ->
    fun e ->
      fun t ->
        (let uu___1 = FStarC_Options.parse_cmd_line () in ());
        (let env = tcenv () in
         (let uu___2 = FStarC_TypeChecker_Core.check_term env e t true in
          match uu___2 with
          | Fstarcompiler.FStar_Pervasives.Inl (FStar_Pervasives_Native.None)
              ->
              let uu___3 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
              FStarC_Format.print1 "%s core typing ok\n" uu___3
          | Fstarcompiler.FStar_Pervasives.Inl (FStar_Pervasives_Native.Some
              g) ->
              ((let uu___4 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                FStarC_Format.print1 "%s core typing produced a guard\n"
                  uu___4);
               FStarC_Effect.op_Colon_Equals success false)
          | Fstarcompiler.FStar_Pervasives.Inr err ->
              (FStarC_Effect.op_Colon_Equals success false;
               (let uu___4 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                let uu___5 = FStarC_TypeChecker_Core.print_error err in
                FStarC_Format.print2 "%s failed\n%s\n" uu___4 uu___5)));
         FStarC_Options.init ())
let (inst :
  Prims.int ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term Prims.list))
  =
  fun n ->
    fun tm ->
      let rec aux out =
        fun n1 ->
          if n1 = Prims.int_zero
          then out
          else
            (let uu___1 =
               let uu___2 = FStarC_Tests_Pars.init () in
               FStarC_TypeChecker_Util.new_implicit_var ""
                 FStarC_Range_Type.dummyRange uu___2
                 FStarC_Syntax_Util.ktype0 false in
             match uu___1 with
             | (t, uu___2, uu___3) ->
                 let uu___4 =
                   let uu___5 = FStarC_Tests_Pars.init () in
                   FStarC_TypeChecker_Util.new_implicit_var ""
                     FStarC_Range_Type.dummyRange uu___5 t false in
                 (match uu___4 with
                  | (u, uu___5, uu___6) ->
                      aux (u :: out) (n1 - Prims.int_one))) in
      let us = aux [] n in
      let uu___ = let uu___1 = FStarC_Tests_Util.app tm us in norm uu___1 in
      (uu___, us)
let (run_all : unit -> Prims.bool) =
  fun uu___ ->
    FStarC_Format.print_string "Testing the unifier\n";
    (let unify_check n =
       fun bvs -> fun x -> fun y -> fun g -> fun f -> unify n bvs x y g f in
     let unify1 n =
       fun bvs ->
         fun x -> fun y -> fun g -> unify n bvs x y g (fun uu___2 -> ()) in
     let int_t = FStarC_Tests_Pars.tc "Prims.int" in
     let x_bv =
       FStarC_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t in
     let y_bv =
       FStarC_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t in
     let x = FStarC_Syntax_Syntax.bv_to_name x_bv in
     let y = FStarC_Syntax_Syntax.bv_to_name y_bv in
     unify1 Prims.int_zero [x_bv] x x FStarC_TypeChecker_Common.Trivial;
     (let uu___4 =
        let uu___5 =
          FStarC_Syntax_Util.mk_eq2 FStarC_Syntax_Syntax.U_zero
            FStarC_Syntax_Util.t_bool x y in
        FStarC_TypeChecker_Common.NonTrivial uu___5 in
      unify1 Prims.int_one [x_bv; y_bv] x y uu___4);
     (let id = FStarC_Tests_Pars.tc "fun (x:bool) -> x" in
      (let uu___5 = FStarC_Tests_Util.app id [x] in
       unify1 (Prims.of_int (2)) [x_bv] x uu___5
         FStarC_TypeChecker_Common.Trivial);
      (let id1 = FStarC_Tests_Pars.tc "fun (x:bool) -> x" in
       unify1 (Prims.of_int (3)) [] id1 id1 FStarC_TypeChecker_Common.Trivial;
       (let id2 = FStarC_Tests_Pars.tc "fun (x:bool) -> x" in
        let id' = FStarC_Tests_Pars.tc "fun (y:bool) -> y" in
        unify1 (Prims.of_int (4)) [] id2 id'
          FStarC_TypeChecker_Common.Trivial;
        (let uu___8 = FStarC_Tests_Pars.tc "fun (x y:bool) -> x" in
         let uu___9 = FStarC_Tests_Pars.tc "fun (a b:bool) -> a" in
         unify1 (Prims.of_int (5)) [] uu___8 uu___9
           FStarC_TypeChecker_Common.Trivial);
        (let uu___9 = FStarC_Tests_Pars.tc "fun (x y z:bool) -> y" in
         let uu___10 = FStarC_Tests_Pars.tc "fun (a b c:bool) -> b" in
         unify1 (Prims.of_int (6)) [] uu___9 uu___10
           FStarC_TypeChecker_Common.Trivial);
        (let uu___10 = FStarC_Tests_Pars.tc "fun (x:int) (y:int) -> y" in
         let uu___11 = FStarC_Tests_Pars.tc "fun (x:int) (y:int) -> x" in
         let uu___12 =
           let uu___13 =
             FStarC_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))" in
           FStarC_TypeChecker_Common.NonTrivial uu___13 in
         unify1 (Prims.of_int (7)) [] uu___10 uu___11 uu___12);
        (let uu___11 =
           FStarC_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y" in
         let uu___12 =
           FStarC_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z" in
         let uu___13 =
           let uu___14 =
             FStarC_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))" in
           FStarC_TypeChecker_Common.NonTrivial uu___14 in
         unify1 (Prims.of_int (8)) [] uu___11 uu___12 uu___13);
        (let uu___12 = FStarC_Options.parse_cmd_line () in ());
        (let uu___12 =
           let uu___13 =
             FStarC_Tests_Pars.tc "fun (u:Type0 -> Type0) (x:Type0) -> u x" in
           inst Prims.int_one uu___13 in
         match uu___12 with
         | (tm, us) ->
             let sol = FStarC_Tests_Pars.tc "fun (x:Type0) -> Prims.pair x x" in
             (unify_check (Prims.of_int (9)) [] tm sol
                FStarC_TypeChecker_Common.Trivial
                (fun uu___14 ->
                   let uu___15 =
                     let uu___16 =
                       let uu___17 = FStarC_List.hd us in norm uu___17 in
                     let uu___17 = norm sol in
                     FStarC_Tests_Util.term_eq uu___16 uu___17 in
                   FStarC_Tests_Util.always (Prims.of_int (9)) uu___15);
              (let uu___14 =
                 let uu___15 =
                   FStarC_Tests_Pars.tc
                     "fun (u: int -> int -> int) (x:int) -> u x" in
                 inst Prims.int_one uu___15 in
               match uu___14 with
               | (tm1, us1) ->
                   let sol1 = FStarC_Tests_Pars.tc "fun (x y:int) -> x + y" in
                   (unify_check (Prims.of_int (10)) [] tm1 sol1
                      FStarC_TypeChecker_Common.Trivial
                      (fun uu___16 ->
                         let uu___17 =
                           let uu___18 =
                             let uu___19 = FStarC_List.hd us1 in norm uu___19 in
                           let uu___19 = norm sol1 in
                           FStarC_Tests_Util.term_eq uu___18 uu___19 in
                         FStarC_Tests_Util.always (Prims.of_int (10)) uu___17);
                    (let tm11 =
                       FStarC_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool" in
                     let tm2 = FStarC_Tests_Pars.tc "x:int -> y:int -> bool" in
                     (let uu___17 =
                        let uu___18 =
                          FStarC_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)" in
                        FStarC_TypeChecker_Common.NonTrivial uu___18 in
                      unify1 (Prims.of_int (11)) [] tm11 tm2 uu___17);
                     (let tm12 =
                        FStarC_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      let tm21 =
                        FStarC_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      unify1 (Prims.of_int (12)) [] tm12 tm21
                        FStarC_TypeChecker_Common.Trivial;
                      (let uu___18 =
                         let int_typ = FStarC_Tests_Pars.tc "int" in
                         let x1 =
                           FStarC_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None int_typ in
                         let typ = FStarC_Tests_Pars.tc "unit -> Type0" in
                         let l =
                           FStarC_Tests_Pars.tc
                             "fun (q:(unit -> Type0)) -> q ()" in
                         let q =
                           FStarC_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None typ in
                         let tm13 =
                           let uu___19 =
                             let uu___20 =
                               let uu___21 =
                                 FStarC_Syntax_Syntax.bv_to_name q in
                               [uu___21] in
                             FStarC_Tests_Util.app l uu___20 in
                           norm uu___19 in
                         let l1 =
                           FStarC_Tests_Pars.tc "fun (p:unit -> Type0) -> p" in
                         let unit = FStarC_Tests_Pars.tc "()" in
                         let env =
                           let uu___19 = FStarC_Tests_Pars.init () in
                           let uu___20 =
                             let uu___21 = FStarC_Syntax_Syntax.mk_binder x1 in
                             let uu___22 =
                               let uu___23 = FStarC_Syntax_Syntax.mk_binder q in
                               [uu___23] in
                             uu___21 :: uu___22 in
                           FStarC_TypeChecker_Env.push_binders uu___19
                             uu___20 in
                         let uu___19 =
                           FStarC_TypeChecker_Util.new_implicit_var ""
                             FStarC_Range_Type.dummyRange env typ false in
                         match uu___19 with
                         | (u_p, uu___20, uu___21) ->
                             let tm22 =
                               let uu___22 =
                                 let uu___23 = FStarC_Tests_Util.app l1 [u_p] in
                                 norm uu___23 in
                               FStarC_Tests_Util.app uu___22 [unit] in
                             (tm13, tm22, [x1; q]) in
                       match uu___18 with
                       | (tm13, tm22, bvs_13) ->
                           (unify1 (Prims.of_int (13)) bvs_13 tm13 tm22
                              FStarC_TypeChecker_Common.Trivial;
                            (let uu___20 =
                               let int_typ = FStarC_Tests_Pars.tc "int" in
                               let x1 =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None int_typ in
                               let typ =
                                 FStarC_Tests_Pars.tc "pure_post unit" in
                               let l =
                                 FStarC_Tests_Pars.tc
                                   "fun (q:pure_post unit) -> q ()" in
                               let q =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None typ in
                               let tm14 =
                                 let uu___21 =
                                   let uu___22 =
                                     let uu___23 =
                                       FStarC_Syntax_Syntax.bv_to_name q in
                                     [uu___23] in
                                   FStarC_Tests_Util.app l uu___22 in
                                 norm uu___21 in
                               let l1 =
                                 FStarC_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p" in
                               let unit = FStarC_Tests_Pars.tc "()" in
                               let env =
                                 let uu___21 = FStarC_Tests_Pars.init () in
                                 let uu___22 =
                                   let uu___23 =
                                     FStarC_Syntax_Syntax.mk_binder x1 in
                                   let uu___24 =
                                     let uu___25 =
                                       FStarC_Syntax_Syntax.mk_binder q in
                                     [uu___25] in
                                   uu___23 :: uu___24 in
                                 FStarC_TypeChecker_Env.push_binders uu___21
                                   uu___22 in
                               let uu___21 =
                                 FStarC_TypeChecker_Util.new_implicit_var ""
                                   FStarC_Range_Type.dummyRange env typ false in
                               match uu___21 with
                               | (u_p, uu___22, uu___23) ->
                                   let tm23 =
                                     let uu___24 =
                                       let uu___25 =
                                         FStarC_Tests_Util.app l1 [u_p] in
                                       norm uu___25 in
                                     FStarC_Tests_Util.app uu___24 [unit] in
                                   (tm14, tm23, [x1; q]) in
                             match uu___20 with
                             | (tm14, tm23, bvs_14) ->
                                 (unify1 (Prims.of_int (14)) bvs_14 tm14 tm23
                                    FStarC_TypeChecker_Common.Trivial;
                                  (let uu___22 =
                                     FStarC_Tests_Pars.pars_and_tc_fragment
                                       "let ty0 n = x:int { x >= n }\nlet ty1 n = x:ty0 n { x > n }\nassume val tc (t:Type0) : Type0";
                                     (let t0 = FStarC_Tests_Pars.tc "ty1 17" in
                                      let t1 =
                                        FStarC_Tests_Pars.tc
                                          "x:ty0 17 { x > 17 }" in
                                      (t0, t1)) in
                                   match uu___22 with
                                   | (tm15, tm24) ->
                                       (check_core (Prims.of_int (15)) false
                                          false tm15 tm24;
                                        (let uu___24 =
                                           let t0 =
                                             FStarC_Tests_Pars.tc
                                               "x:int { x >= 17 /\\ x > 17 }" in
                                           let t1 =
                                             FStarC_Tests_Pars.tc
                                               "x:ty0 17 { x > 17 }" in
                                           (t0, t1) in
                                         match uu___24 with
                                         | (tm16, tm25) ->
                                             (check_core (Prims.of_int (16))
                                                false false tm16 tm25;
                                              (let uu___26 =
                                                 FStarC_Tests_Pars.pars_and_tc_fragment
                                                   "let defn17_0 (x:nat) : nat -> nat -> Type0 = fun y z -> a:int { a + x == y + z }";
                                                 (let t0 =
                                                    FStarC_Tests_Pars.tc
                                                      "defn17_0 0 1 2" in
                                                  let t1_head =
                                                    FStarC_Tests_Pars.tc
                                                      "(defn17_0 0)" in
                                                  let arg1 =
                                                    FStarC_Tests_Pars.tc "1" in
                                                  let arg2 =
                                                    FStarC_Tests_Pars.tc "2" in
                                                  let t1 =
                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                      t1_head
                                                      [(arg1,
                                                         FStar_Pervasives_Native.None);
                                                      (arg2,
                                                        FStar_Pervasives_Native.None)]
                                                      t0.FStarC_Syntax_Syntax.pos in
                                                  (t0, t1)) in
                                               match uu___26 with
                                               | (tm17, tm26) ->
                                                   (check_core
                                                      (Prims.of_int (17))
                                                      false false tm17 tm26;
                                                    (let uu___28 =
                                                       let t0 =
                                                         FStarC_Tests_Pars.tc
                                                           "dp:((dtuple2 int (fun (y:int) -> z:int{ z > y })) <: Type0) { let (| x, _ |) = dp in x > 17 }" in
                                                       let t1 =
                                                         FStarC_Tests_Pars.tc
                                                           "(dtuple2 int (fun (y:int) -> z:int{ z > y }))" in
                                                       (t0, t1) in
                                                     match uu___28 with
                                                     | (tm18, tm27) ->
                                                         (check_core
                                                            (Prims.of_int (18))
                                                            true false tm18
                                                            tm27;
                                                          (let uu___30 =
                                                             FStarC_Tests_Pars.pars_and_tc_fragment
                                                               "type vprop' = { t:Type0 ; n:nat }";
                                                             (let t0 =
                                                                FStarC_Tests_Pars.tc
                                                                  "x:(({ t=bool; n=0 }).t <: Type0) { x == false }" in
                                                              let t1 =
                                                                FStarC_Tests_Pars.tc
                                                                  "x:bool{ x == false }" in
                                                              (t0, t1)) in
                                                           match uu___30 with
                                                           | (tm19, tm28) ->
                                                               (check_core
                                                                  (Prims.of_int (19))
                                                                  false false
                                                                  tm19 tm28;
                                                                (let uu___32
                                                                   =
                                                                   let t0 =
                                                                    FStarC_Tests_Pars.tc
                                                                    "int" in
                                                                   let t1 =
                                                                    FStarC_Tests_Pars.tc
                                                                    "j:(i:nat{ i > 17 } <: Type0){j > 42}" in
                                                                   (t0, t1) in
                                                                 match uu___32
                                                                 with
                                                                 | (tm110,
                                                                    tm29) ->
                                                                    (check_core
                                                                    (Prims.of_int (20))
                                                                    true true
                                                                    tm110
                                                                    tm29;
                                                                    (let uu___34
                                                                    =
                                                                    FStarC_Tests_Pars.pars_and_tc_fragment
                                                                    "assume val tstr21 (x:string) : Type0";
                                                                    (
                                                                    let t0 =
                                                                    FStarC_Tests_Pars.tc
                                                                    "(fun (x:bool) (y:int) (z: (fun (x:string) -> tstr21 x) \"hello\") -> x)" in
                                                                    let ty =
                                                                    FStarC_Tests_Pars.tc
                                                                    "bool -> int -> tstr21 \"hello\" -> bool" in
                                                                    (t0, ty)) in
                                                                    match uu___34
                                                                    with
                                                                    | 
                                                                    (tm3, ty)
                                                                    ->
                                                                    (check_core_typing
                                                                    (Prims.of_int (21))
                                                                    tm3 ty;
                                                                    (let uu___37
                                                                    =
                                                                    FStarC_Effect.op_Bang
                                                                    success in
                                                                    if
                                                                    uu___37
                                                                    then
                                                                    FStarC_Format.print_string
                                                                    "Unifier ok\n"
                                                                    else ());
                                                                    FStarC_Effect.op_Bang
                                                                    success))))))))))))))))))))))))))))
