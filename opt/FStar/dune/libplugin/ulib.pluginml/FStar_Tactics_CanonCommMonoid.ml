open Fstarcompiler
open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    fun ps ->
      let x = FStarC_Tactics_V2_Builtins.debugging () ps in
      if x then FStarC_Tactics_V2_Builtins.dump m ps else ()
type var = Prims.nat
type exp =
  | Unit 
  | Var of var 
  | Mult of exp * exp 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Var : exp -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : exp -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let rec (exp_to_string : exp -> Prims.string) =
  fun e ->
    match e with
    | Unit -> "Unit"
    | Var x -> Prims.strcat "Var " (Prims.string_of_int x)
    | Mult (e1, e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type ('a, 'b) vmap = ((var * ('a * 'b)) Prims.list * ('a * 'b))
let const : 'a 'b . 'a -> 'b -> ('a, 'b) vmap =
  fun xa -> fun xb -> ([], (xa, xb))
let select : 'a 'b . var -> ('a, 'b) vmap -> 'a =
  fun x ->
    fun vm ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (a1, uu___) -> a1
      | uu___ -> FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd vm)
let select_extra : 'a 'b . var -> ('a, 'b) vmap -> 'b =
  fun x ->
    fun vm ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (uu___, b1) -> b1
      | uu___ -> FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd vm)
let update : 'a 'b . var -> 'a -> 'b -> ('a, 'b) vmap -> ('a, 'b) vmap =
  fun x ->
    fun xa ->
      fun xb ->
        fun vm ->
          (((x, (xa, xb)) :: (FStar_Pervasives_Native.fst vm)),
            (FStar_Pervasives_Native.snd vm))
let rec mdenote :
  'a 'b . 'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> exp -> 'a =
  fun m ->
    fun vm ->
      fun e ->
        match e with
        | Unit -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Var x -> select x vm
        | Mult (e1, e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m vm e1) (mdenote m vm e2)
let rec xsdenote :
  'a 'b .
    'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> var Prims.list -> 'a
  =
  fun m ->
    fun vm ->
      fun xs ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x vm
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x vm)
              (xsdenote m vm xs')
let rec (flatten : exp -> var Prims.list) =
  fun e ->
    match e with
    | Unit -> []
    | Var x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
type 'b permute =
  unit -> (Obj.t, 'b) vmap -> var Prims.list -> var Prims.list
type ('b, 'p) permute_correct = unit
type ('b, 'p) permute_via_swaps = unit

let (sort : unit permute) =
  fun a ->
    fun vm ->
      FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))
let sortWith : 'b . (Prims.nat -> Prims.nat -> Prims.int) -> 'b permute =
  fun f -> fun a -> fun vm -> FStar_List_Tot_Base.sortWith f


let canon : 'a 'b . ('a, 'b) vmap -> 'b permute -> exp -> var Prims.list =
  fun vm -> fun p -> fun e -> p () (Obj.magic vm) (flatten e)
let rec (where_aux :
  Prims.nat ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term Prims.list ->
        (Prims.nat FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun n ->
           fun x ->
             fun xs ->
               match xs with
               | [] ->
                   Obj.magic
                     (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
               | x'::xs' ->
                   Obj.magic
                     (Obj.repr
                        (if term_eq x x'
                         then
                           Obj.repr
                             (fun uu___ -> FStar_Pervasives_Native.Some n)
                         else Obj.repr (where_aux (n + Prims.int_one) x xs'))))
          uu___2 uu___1 uu___
let (where :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  = where_aux Prims.int_zero
let rec reification_aux :
  'a 'b .
    (FStar_Tactics_NamedView.term -> ('a, unit) FStar_Tactics_Effect.tac_repr)
      ->
      FStar_Tactics_NamedView.term Prims.list ->
        ('a, 'b) vmap ->
          (FStar_Tactics_NamedView.term ->
             ('b, unit) FStar_Tactics_Effect.tac_repr)
            ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  ((exp * FStar_Tactics_NamedView.term Prims.list * (
                     'a, 'b) vmap),
                    unit) FStar_Tactics_Effect.tac_repr
  =
  fun unquotea ->
    fun ts ->
      fun vm ->
        fun f ->
          fun mult ->
            fun unit ->
              fun t ->
                fun ps ->
                  let x =
                    FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t in
                  match x with
                  | (hd, tl) ->
                      let x1 t1 =
                        fun ts1 ->
                          fun vm1 ->
                            fun ps1 ->
                              let x2 = where t1 ts1 ps1 in
                              match x2 with
                              | FStar_Pervasives_Native.Some v ->
                                  ((Var v), ts1, vm1)
                              | FStar_Pervasives_Native.None ->
                                  let x3 = FStar_List_Tot_Base.length ts1 in
                                  let x4 = unquotea t1 ps1 in
                                  let x5 =
                                    let x6 = f t1 ps1 in update x3 x4 x6 vm1 in
                                  ((Var x3),
                                    (FStar_List_Tot_Base.op_At ts1 [t1]), x5) in
                      let x2 =
                        let x3 = FStar_Tactics_NamedView.inspect hd ps in
                        (x3, (FStar_List_Tot_Base.list_unref tl)) in
                      (match x2 with
                       | (FStar_Tactics_NamedView.Tv_FVar fv,
                          (t1, FStarC_Reflection_V2_Data.Q_Explicit)::
                          (t2, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
                           if
                             term_eq
                               (FStar_Tactics_NamedView.pack
                                  (FStar_Tactics_NamedView.Tv_FVar fv)) mult
                           then
                             let x3 =
                               reification_aux unquotea ts vm f mult unit t1
                                 ps in
                             (match x3 with
                              | (e1, ts1, vm1) ->
                                  let x4 =
                                    reification_aux unquotea ts1 vm1 f mult
                                      unit t2 ps in
                                  (match x4 with
                                   | (e2, ts2, vm2) ->
                                       ((Mult (e1, e2)), ts2, vm2)))
                           else x1 t ts vm ps
                       | (uu___, uu___1) ->
                           if term_eq t unit
                           then (Unit, ts, vm)
                           else x1 t ts vm ps)
let reification :
  'b .
    (FStar_Tactics_NamedView.term -> ('b, unit) FStar_Tactics_Effect.tac_repr)
      ->
      'b ->
        unit ->
          (FStar_Tactics_NamedView.term ->
             (Obj.t, unit) FStar_Tactics_Effect.tac_repr)
            ->
            (Obj.t ->
               (FStar_Tactics_NamedView.term, unit)
                 FStar_Tactics_Effect.tac_repr)
              ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  Obj.t ->
                    FStar_Tactics_NamedView.term Prims.list ->
                      ((exp Prims.list * (Obj.t, 'b) vmap), unit)
                        FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun def ->
      fun a ->
        fun unquotea ->
          fun quotea ->
            fun tmult ->
              fun tunit ->
                fun munit ->
                  fun ts ->
                    fun ps ->
                      let x =
                        FStar_Tactics_V2_Derived.norm_term
                          [Fstarcompiler.FStarC_NormSteps.delta;
                          Fstarcompiler.FStarC_NormSteps.zeta;
                          Fstarcompiler.FStarC_NormSteps.iota] tmult ps in
                      let x1 =
                        FStar_Tactics_V2_Derived.norm_term
                          [Fstarcompiler.FStarC_NormSteps.delta;
                          Fstarcompiler.FStarC_NormSteps.zeta;
                          Fstarcompiler.FStarC_NormSteps.iota] tunit ps in
                      let x2 =
                        FStar_Tactics_Util.map
                          (FStar_Tactics_V2_Derived.norm_term
                             [Fstarcompiler.FStarC_NormSteps.delta;
                             Fstarcompiler.FStarC_NormSteps.zeta;
                             Fstarcompiler.FStarC_NormSteps.iota]) ts ps in
                      let x3 =
                        FStar_Tactics_Util.fold_left
                          (fun uu___ ->
                             fun t ->
                               match uu___ with
                               | (es, vs, vm) ->
                                   (fun ps1 ->
                                      let x4 =
                                        reification_aux unquotea vs vm f x x1
                                          t ps1 in
                                      match x4 with
                                      | (e, vs1, vm1) ->
                                          ((e :: es), vs1, vm1)))
                          ([], [], (const munit def)) x2 ps in
                      match x3 with
                      | (es, uu___, vm) -> ((FStar_List_Tot_Base.rev es), vm)
let rec (term_mem :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun x ->
         fun uu___ ->
           match uu___ with
           | [] -> Obj.magic (Obj.repr (fun uu___1 -> false))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (if term_eq hd x
                     then Obj.repr (fun uu___1 -> true)
                     else Obj.repr (term_mem x tl)))) uu___1 uu___
let (unfold_topdown :
  FStar_Tactics_NamedView.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ts ->
    fun ps ->
      let x s = fun ps1 -> let x1 = term_mem s ts ps1 in (x1, Prims.int_zero) in
      let x1 uu___ =
        fun ps1 ->
          FStarC_Tactics_V2_Builtins.norm
            [Fstarcompiler.FStarC_NormSteps.delta] ps1;
          FStar_Tactics_V2_Derived.trefl () ps1 in
      FStar_Tactics_V2_Derived.topdown_rewrite x x1 ps
let rec quote_list :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        'a Prims.list ->
          (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ta ->
           fun quotea ->
             fun xs ->
               match xs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (fun uu___ ->
                           FStar_Reflection_V2_Derived.mk_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["Prims"; "Nil"])))
                             [(ta, FStarC_Reflection_V2_Data.Q_Implicit)]))
               | x::xs' ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x1 =
                             let x2 =
                               let x3 =
                                 let x4 = quotea x ps in
                                 (x4, FStarC_Reflection_V2_Data.Q_Explicit) in
                               let x4 =
                                 let x5 =
                                   let x6 = quote_list ta quotea xs' ps in
                                   (x6, FStarC_Reflection_V2_Data.Q_Explicit) in
                                 [x5] in
                               x3 :: x4 in
                             (ta, FStarC_Reflection_V2_Data.Q_Implicit) :: x2 in
                           FStar_Reflection_V2_Derived.mk_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["Prims"; "Cons"]))) x1))) uu___2
          uu___1 uu___
let quote_vm :
  'a 'b .
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        ('a ->
           (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          ('b ->
             (FStar_Tactics_NamedView.term, unit)
               FStar_Tactics_Effect.tac_repr)
            ->
            ('a, 'b) vmap ->
              (FStar_Tactics_NamedView.term, unit)
                FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun tb ->
      fun quotea ->
        fun quoteb ->
          fun vm ->
            fun ps ->
              let x p =
                fun ps1 ->
                  let x1 =
                    let x2 =
                      let x3 =
                        let x4 =
                          let x5 = quotea (FStar_Pervasives_Native.fst p) ps1 in
                          (x5, FStarC_Reflection_V2_Data.Q_Explicit) in
                        let x5 =
                          let x6 =
                            let x7 =
                              quoteb (FStar_Pervasives_Native.snd p) ps1 in
                            (x7, FStarC_Reflection_V2_Data.Q_Explicit) in
                          [x6] in
                        x4 :: x5 in
                      (tb, FStarC_Reflection_V2_Data.Q_Implicit) :: x3 in
                    (ta, FStarC_Reflection_V2_Data.Q_Implicit) :: x2 in
                  FStar_Reflection_V2_Derived.mk_app
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar"; "Pervasives"; "Native"; "Mktuple2"])))
                    x1 in
              let x1 =
                FStar_Reflection_V2_Derived.mk_e_app
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Pervasives"; "Native"; "tuple2"])))
                  [ta; tb] in
              let x2 p =
                fun ps1 ->
                  let x3 =
                    let x4 =
                      let x5 =
                        let x6 =
                          let x7 =
                            let x8 = x (FStar_Pervasives_Native.snd p) ps1 in
                            (x8, FStarC_Reflection_V2_Data.Q_Explicit) in
                          [x7] in
                        ((FStar_Tactics_NamedView.pack
                            (FStar_Tactics_NamedView.Tv_Const
                               (FStarC_Reflection_V2_Data.C_Int
                                  (FStar_Pervasives_Native.fst p)))),
                          FStarC_Reflection_V2_Data.Q_Explicit) :: x6 in
                      (x1, FStarC_Reflection_V2_Data.Q_Implicit) :: x5 in
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["Prims"; "nat"]))),
                      FStarC_Reflection_V2_Data.Q_Implicit) :: x4 in
                  FStar_Reflection_V2_Derived.mk_app
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar"; "Pervasives"; "Native"; "Mktuple2"])))
                    x3 in
              let x3 =
                FStar_Reflection_V2_Derived.mk_e_app
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Pervasives"; "Native"; "tuple2"])))
                  [FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["Prims"; "nat"]));
                  x1] in
              let x4 = quote_list x3 x2 (FStar_Pervasives_Native.fst vm) ps in
              let x5 = x (FStar_Pervasives_Native.snd vm) ps in
              FStar_Reflection_V2_Derived.mk_app
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "Pervasives"; "Native"; "Mktuple2"])))
                [((FStar_Reflection_V2_Derived.mk_e_app
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["Prims"; "list"]))) [x3]),
                   FStarC_Reflection_V2_Data.Q_Implicit);
                (x1, FStarC_Reflection_V2_Data.Q_Implicit);
                (x4, FStarC_Reflection_V2_Data.Q_Explicit);
                (x5, FStarC_Reflection_V2_Data.Q_Explicit)]
let rec (quote_exp :
  exp -> (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun e ->
       match e with
       | Unit ->
           Obj.magic
             (Obj.repr
                (fun uu___ ->
                   FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "CanonCommMonoid"; "Unit"]))))
       | Var x ->
           Obj.magic
             (Obj.repr
                (fun uu___ ->
                   FStar_Reflection_V2_Derived.mk_e_app
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "CanonCommMonoid"; "Var"])))
                     [FStar_Tactics_NamedView.pack
                        (FStar_Tactics_NamedView.Tv_Const
                           (FStarC_Reflection_V2_Data.C_Int x))]))
       | Mult (e1, e2) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x =
                     let x1 = quote_exp e1 ps in
                     let x2 = let x3 = quote_exp e2 ps in [x3] in x1 :: x2 in
                   FStar_Reflection_V2_Derived.mk_e_app
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "CanonCommMonoid"; "Mult"])))
                     x))) uu___
let canon_monoid_aux :
  'a 'b .
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term ->
         ('a, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ('a ->
           (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                'a ->
                  FStar_Tactics_NamedView.term ->
                    ('b ->
                       (FStar_Tactics_NamedView.term, unit)
                         FStar_Tactics_Effect.tac_repr)
                      ->
                      (FStar_Tactics_NamedView.term ->
                         ('b, unit) FStar_Tactics_Effect.tac_repr)
                        ->
                        'b ->
                          FStar_Tactics_NamedView.term ->
                            FStar_Tactics_NamedView.term ->
                              (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun unquotea ->
      fun quotea ->
        fun tm ->
          fun tmult ->
            fun tunit ->
              fun munit ->
                fun tb ->
                  fun quoteb ->
                    fun f ->
                      fun def ->
                        fun tp ->
                          fun tpc ->
                            fun ps ->
                              FStarC_Tactics_V2_Builtins.norm [] ps;
                              (let x1 =
                                 let x2 =
                                   FStar_Tactics_V2_Derived.cur_goal () ps in
                                 FStar_Reflection_V2_Formula.term_as_formula
                                   x2 ps in
                               match x1 with
                               | FStar_Reflection_V2_Formula.Comp
                                   (FStar_Reflection_V2_Formula.Eq
                                    (FStar_Pervasives_Native.Some t), t1, t2)
                                   ->
                                   if term_eq t ta
                                   then
                                     let x2 =
                                       Obj.magic
                                         (reification f def ()
                                            (fun uu___ ->
                                               (Obj.magic unquotea) uu___)
                                            (fun uu___ ->
                                               (Obj.magic quotea) uu___)
                                            tmult tunit (Obj.magic munit)
                                            [t1; t2] ps) in
                                     (match x2 with
                                      | (r1::r2::[], vm) ->
                                          let x3 =
                                            quote_vm ta tb quotea quoteb vm
                                              ps in
                                          let x4 = quote_exp r1 ps in
                                          let x5 = quote_exp r2 ps in
                                          let x6 =
                                            FStar_Reflection_V2_Derived.mk_app
                                              (FStarC_Reflection_V2_Builtins.pack_ln
                                                 (FStarC_Reflection_V2_Data.Tv_FVar
                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                       ["Prims"; "eq2"])))
                                              [(ta,
                                                 FStarC_Reflection_V2_Data.Q_Implicit);
                                              ((FStar_Reflection_V2_Derived.mk_app
                                                  (FStarC_Reflection_V2_Builtins.pack_ln
                                                     (FStarC_Reflection_V2_Data.Tv_FVar
                                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                                           ["FStar";
                                                           "Tactics";
                                                           "CanonCommMonoid";
                                                           "mdenote"])))
                                                  [(ta,
                                                     FStarC_Reflection_V2_Data.Q_Implicit);
                                                  (tb,
                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                  (tm,
                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                  (x3,
                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                  (x4,
                                                    FStarC_Reflection_V2_Data.Q_Explicit)]),
                                                FStarC_Reflection_V2_Data.Q_Explicit);
                                              ((FStar_Reflection_V2_Derived.mk_app
                                                  (FStarC_Reflection_V2_Builtins.pack_ln
                                                     (FStarC_Reflection_V2_Data.Tv_FVar
                                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                                           ["FStar";
                                                           "Tactics";
                                                           "CanonCommMonoid";
                                                           "mdenote"])))
                                                  [(ta,
                                                     FStarC_Reflection_V2_Data.Q_Implicit);
                                                  (tb,
                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                  (tm,
                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                  (x3,
                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                  (x5,
                                                    FStarC_Reflection_V2_Data.Q_Explicit)]),
                                                FStarC_Reflection_V2_Data.Q_Explicit)] in
                                          (FStar_Tactics_V2_Derived.change_sq
                                             x6 ps;
                                           FStar_Tactics_MApply0.mapply0
                                             (FStar_Reflection_V2_Derived.mk_app
                                                (FStarC_Reflection_V2_Builtins.pack_ln
                                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                                         ["FStar";
                                                         "Tactics";
                                                         "CanonCommMonoid";
                                                         "monoid_reflect"])))
                                                [(ta,
                                                   FStarC_Reflection_V2_Data.Q_Implicit);
                                                (tb,
                                                  FStarC_Reflection_V2_Data.Q_Implicit);
                                                (tp,
                                                  FStarC_Reflection_V2_Data.Q_Explicit);
                                                (tpc,
                                                  FStarC_Reflection_V2_Data.Q_Explicit)])
                                             ps;
                                           unfold_topdown
                                             [FStarC_Reflection_V2_Builtins.pack_ln
                                                (FStarC_Reflection_V2_Data.Tv_FVar
                                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                                      ["FStar";
                                                      "Tactics";
                                                      "CanonCommMonoid";
                                                      "canon"]));
                                             FStarC_Reflection_V2_Builtins.pack_ln
                                               (FStarC_Reflection_V2_Data.Tv_FVar
                                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                                     ["FStar";
                                                     "Tactics";
                                                     "CanonCommMonoid";
                                                     "xsdenote"]));
                                             tp] ps;
                                           FStarC_Tactics_V2_Builtins.norm
                                             [Fstarcompiler.FStarC_NormSteps.delta_only
                                                ["FStar.Tactics.CanonCommMonoid.canon";
                                                "FStar.Tactics.CanonCommMonoid.xsdenote";
                                                "FStar.Tactics.CanonCommMonoid.flatten";
                                                "FStar.Tactics.CanonCommMonoid.select";
                                                "FStar.Tactics.CanonCommMonoid.select_extra";
                                                "FStar.Tactics.CanonCommMonoid.quote_list";
                                                "FStar.Tactics.CanonCommMonoid.quote_vm";
                                                "FStar.Tactics.CanonCommMonoid.quote_exp";
                                                "FStar.Tactics.CanonCommMonoid.const_compare";
                                                "FStar.Tactics.CanonCommMonoid.special_compare";
                                                "FStar.Pervasives.Native.fst";
                                                "FStar.Pervasives.Native.snd";
                                                "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
                                                "FStar.List.Tot.Base.assoc";
                                                "FStar.List.Tot.Base.op_At";
                                                "FStar.List.Tot.Base.append";
                                                "SL.AutoTactic.compare_b";
                                                "SL.AutoTactic.compare_v";
                                                "FStar.Order.int_of_order";
                                                "FStar.Reflection.V2.Compare.compare_term";
                                                "FStar.List.Tot.Base.sortWith";
                                                "FStar.List.Tot.Base.partition";
                                                "FStar.List.Tot.Base.bool_of_compare";
                                                "FStar.List.Tot.Base.compare_of_bool"];
                                             Fstarcompiler.FStarC_NormSteps.zeta;
                                             Fstarcompiler.FStarC_NormSteps.iota;
                                             Fstarcompiler.FStarC_NormSteps.primops]
                                             ps)
                                      | uu___ ->
                                          FStar_Tactics_V2_Derived.fail
                                            "Unexpected" ps)
                                   else
                                     FStar_Tactics_V2_Derived.fail
                                       "Goal should be an equality at the right monoid type"
                                       ps
                               | uu___ ->
                                   FStar_Tactics_V2_Derived.fail
                                     "Goal should be an equality" ps)
let canon_monoid_with :
  'b .
    (FStar_Tactics_NamedView.term -> ('b, unit) FStar_Tactics_Effect.tac_repr)
      ->
      'b ->
        'b permute ->
          unit ->
            unit ->
              Obj.t FStar_Algebra_CommMonoid.cm ->
                (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun def ->
      fun p ->
        fun pc ->
          fun a ->
            fun m ->
              fun ps ->
                let x =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                let x1 =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                let x2 =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                let x3 =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                let x4 =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                let x5 =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                let x6 =
                  Obj.magic
                    (failwith "Cannot evaluate open quotation at runtime") in
                canon_monoid_aux x FStarC_Tactics_V2_Builtins.unquote
                  (fun uu___ ->
                     (fun x7 ->
                        Obj.magic
                          (fun uu___ ->
                             Obj.magic
                               (failwith
                                  "Cannot evaluate open quotation at runtime")))
                       uu___) x1 x2 x3
                  (FStar_Algebra_CommMonoid.__proj__CM__item__unit m) x4
                  (fun uu___ ->
                     (fun x7 ->
                        Obj.magic
                          (fun uu___ ->
                             Obj.magic
                               (failwith
                                  "Cannot evaluate open quotation at runtime")))
                       uu___) f def x5 x6 ps
let canon_monoid :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun cm ->
    canon_monoid_with
      (fun uu___ -> (fun uu___ -> Obj.magic (fun uu___1 -> ())) uu___) ()
      (fun a1 -> sort ()) () () (Obj.magic cm)
let (is_const :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ps ->
      let x = FStar_Tactics_NamedView.inspect t ps in
      FStar_Tactics_NamedView.uu___is_Tv_Const x
let const_compare : 'a . ('a, Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm ->
    fun x ->
      fun y ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false, false) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false, true) -> Prims.int_one
        | (true, false) -> (Prims.of_int (-1))
let const_last :
  'a . ('a, Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm -> fun xs -> FStar_List_Tot_Base.sortWith (const_compare vm) xs
let canon_monoid_const :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun cm ->
    canon_monoid_with is_const false (fun a1 -> const_last) () ()
      (Obj.magic cm)
let (is_special :
  FStar_Tactics_NamedView.term Prims.list ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = fun ts -> fun t -> term_mem t ts
let special_compare : 'a . ('a, Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm ->
    fun x ->
      fun y ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false, false) -> Prims.int_zero
        | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false, true) -> (Prims.of_int (-1))
        | (true, false) -> Prims.int_one
let special_first :
  'a . ('a, Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm -> fun xs -> FStar_List_Tot_Base.sortWith (special_compare vm) xs

let canon_monoid_special :
  'uuuuu .
    FStar_Tactics_NamedView.term Prims.list ->
      'uuuuu FStar_Algebra_CommMonoid.cm ->
        (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ts ->
         Obj.magic
           (canon_monoid_with (is_special ts) false (fun a -> special_first)
              () ())) uu___1 uu___
