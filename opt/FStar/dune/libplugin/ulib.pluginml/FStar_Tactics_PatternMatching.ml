open Fstarcompiler
open Prims
let (fetch_eq_side :
  unit ->
    ((FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    fun ps ->
      let x = FStar_Tactics_V2_Derived.cur_goal () ps in
      let x1 = FStar_Tactics_NamedView.inspect x ps in
      match x1 with
      | FStar_Tactics_NamedView.Tv_App (squash, (g, uu___1)) ->
          let x2 = FStar_Tactics_NamedView.inspect squash ps in
          (match x2 with
           | FStar_Tactics_NamedView.Tv_UInst (squash1, uu___2) ->
               if
                 (FStar_Reflection_V2_Derived.fv_to_string squash1) =
                   (FStar_Reflection_V2_Derived.flatten_name
                      FStar_Reflection_Const.squash_qn)
               then
                 let x3 = FStar_Tactics_NamedView.inspect g ps in
                 (match x3 with
                  | FStar_Tactics_NamedView.Tv_App (eq_type_x, (y, uu___3))
                      ->
                      let x4 = FStar_Tactics_NamedView.inspect eq_type_x ps in
                      (match x4 with
                       | FStar_Tactics_NamedView.Tv_App
                           (eq_type, (x5, uu___4)) ->
                           let x6 =
                             FStar_Tactics_NamedView.inspect eq_type ps in
                           (match x6 with
                            | FStar_Tactics_NamedView.Tv_App
                                (eq, (typ, uu___5)) ->
                                let x7 =
                                  FStar_Tactics_NamedView.inspect eq ps in
                                (match x7 with
                                 | FStar_Tactics_NamedView.Tv_UInst
                                     (eq1, uu___6) ->
                                     if
                                       (FStar_Reflection_V2_Derived.fv_to_string
                                          eq1)
                                         =
                                         (FStar_Reflection_V2_Derived.flatten_name
                                            FStar_Reflection_Const.eq2_qn)
                                     then (x5, y)
                                     else
                                       FStar_Tactics_V2_Derived.fail
                                         "not an equality" ps
                                 | FStar_Tactics_NamedView.Tv_FVar eq1 ->
                                     if
                                       (FStar_Reflection_V2_Derived.fv_to_string
                                          eq1)
                                         =
                                         (FStar_Reflection_V2_Derived.flatten_name
                                            FStar_Reflection_Const.eq2_qn)
                                     then (x5, y)
                                     else
                                       FStar_Tactics_V2_Derived.fail
                                         "not an equality" ps
                                 | uu___6 ->
                                     FStar_Tactics_V2_Derived.fail
                                       "not an app2 of fvar: " ps)
                            | uu___5 ->
                                FStar_Tactics_V2_Derived.fail "not an app3"
                                  ps)
                       | uu___4 ->
                           FStar_Tactics_V2_Derived.fail "not an app2" ps)
                  | uu___3 ->
                      FStar_Tactics_V2_Derived.fail "not an app under squash"
                        ps)
               else FStar_Tactics_V2_Derived.fail "not a squash" ps
           | FStar_Tactics_NamedView.Tv_FVar squash1 ->
               if
                 (FStar_Reflection_V2_Derived.fv_to_string squash1) =
                   (FStar_Reflection_V2_Derived.flatten_name
                      FStar_Reflection_Const.squash_qn)
               then
                 let x3 = FStar_Tactics_NamedView.inspect g ps in
                 (match x3 with
                  | FStar_Tactics_NamedView.Tv_App (eq_type_x, (y, uu___2))
                      ->
                      let x4 = FStar_Tactics_NamedView.inspect eq_type_x ps in
                      (match x4 with
                       | FStar_Tactics_NamedView.Tv_App
                           (eq_type, (x5, uu___3)) ->
                           let x6 =
                             FStar_Tactics_NamedView.inspect eq_type ps in
                           (match x6 with
                            | FStar_Tactics_NamedView.Tv_App
                                (eq, (typ, uu___4)) ->
                                let x7 =
                                  FStar_Tactics_NamedView.inspect eq ps in
                                (match x7 with
                                 | FStar_Tactics_NamedView.Tv_UInst
                                     (eq1, uu___5) ->
                                     if
                                       (FStar_Reflection_V2_Derived.fv_to_string
                                          eq1)
                                         =
                                         (FStar_Reflection_V2_Derived.flatten_name
                                            FStar_Reflection_Const.eq2_qn)
                                     then (x5, y)
                                     else
                                       FStar_Tactics_V2_Derived.fail
                                         "not an equality" ps
                                 | FStar_Tactics_NamedView.Tv_FVar eq1 ->
                                     if
                                       (FStar_Reflection_V2_Derived.fv_to_string
                                          eq1)
                                         =
                                         (FStar_Reflection_V2_Derived.flatten_name
                                            FStar_Reflection_Const.eq2_qn)
                                     then (x5, y)
                                     else
                                       FStar_Tactics_V2_Derived.fail
                                         "not an equality" ps
                                 | uu___5 ->
                                     FStar_Tactics_V2_Derived.fail
                                       "not an app2 of fvar: " ps)
                            | uu___4 ->
                                FStar_Tactics_V2_Derived.fail "not an app3"
                                  ps)
                       | uu___3 ->
                           FStar_Tactics_V2_Derived.fail "not an app2" ps)
                  | uu___2 ->
                      FStar_Tactics_V2_Derived.fail "not an app under squash"
                        ps)
               else FStar_Tactics_V2_Derived.fail "not a squash" ps
           | uu___2 ->
               FStar_Tactics_V2_Derived.fail
                 "not an app of fvar at top level" ps)
      | uu___1 -> FStar_Tactics_V2_Derived.fail "not an app at top level" ps
let mustfail :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    fun message ->
      fun ps ->
        let x = FStar_Tactics_V2_Derived.trytac t ps in
        match x with
        | FStar_Pervasives_Native.Some uu___ ->
            FStar_Tactics_V2_Derived.fail message ps
        | FStar_Pervasives_Native.None -> ()
let (implies_intro' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    fun ps -> let x = FStar_Tactics_V2_Logic.implies_intro () ps in ()
let repeat' :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  = fun f -> fun ps -> let x = FStar_Tactics_V2_Derived.repeat f ps in ()
let (and_elim' :
  FStar_Tactics_NamedView.binding ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun h ->
    fun ps ->
      FStar_Tactics_V2_Logic.and_elim
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_Var
              (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv h))) ps;
      FStarC_Tactics_V2_Builtins.clear h ps
let exact_hyp :
  'a .
    FStar_Tactics_NamedView.namedv ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun h ->
    fun ps ->
      let x =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.exact
        (FStar_Reflection_V2_Derived.mk_app x
           [((FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_Var h)),
              FStarC_Reflection_V2_Data.Q_Explicit)]) ps
let (exact_hyp' :
  FStar_Tactics_NamedView.namedv ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun h ->
    FStar_Tactics_V2_Derived.exact
      (FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_Var h))
type varname = Prims.string
type qn = Prims.string
type pattern =
  | PVar of varname 
  | PQn of qn 
  | PType 
  | PApp of pattern * pattern 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PVar name -> true | uu___ -> false
let (__proj__PVar__item__name : pattern -> varname) =
  fun projectee -> match projectee with | PVar name -> name
let (uu___is_PQn : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PQn qn1 -> true | uu___ -> false
let (__proj__PQn__item__qn : pattern -> qn) =
  fun projectee -> match projectee with | PQn qn1 -> qn1
let (uu___is_PType : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PType -> true | uu___ -> false
let (uu___is_PApp : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PApp (hd, arg) -> true | uu___ -> false
let (__proj__PApp__item__hd : pattern -> pattern) =
  fun projectee -> match projectee with | PApp (hd, arg) -> hd
let (__proj__PApp__item__arg : pattern -> pattern) =
  fun projectee -> match projectee with | PApp (hd, arg) -> arg
let (desc_of_pattern : pattern -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | PVar uu___1 -> "a variable"
    | PQn qn1 -> Prims.strcat "a constant (" (Prims.strcat qn1 ")")
    | PType -> "Type"
    | PApp (uu___1, uu___2) -> "a function application"
let rec (string_of_pattern : pattern -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | PVar x -> Prims.strcat "?" x
    | PQn qn1 -> qn1
    | PType -> "Type"
    | PApp (l, r) ->
        Prims.strcat "("
          (Prims.strcat (string_of_pattern l)
             (Prims.strcat " " (Prims.strcat (string_of_pattern r) ")")))
type match_exception =
  | NameMismatch of (qn * qn) 
  | SimpleMismatch of (pattern * FStar_Tactics_NamedView.term) 
  | NonLinearMismatch of (varname * FStar_Tactics_NamedView.term *
  FStar_Tactics_NamedView.term) 
  | UnsupportedTermInPattern of FStar_Tactics_NamedView.term 
  | IncorrectTypeInAbsPatBinder of FStarC_Reflection_Types.typ 
let (uu___is_NameMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NameMismatch _0 -> true | uu___ -> false
let (__proj__NameMismatch__item___0 : match_exception -> (qn * qn)) =
  fun projectee -> match projectee with | NameMismatch _0 -> _0
let (uu___is_SimpleMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleMismatch _0 -> true | uu___ -> false
let (__proj__SimpleMismatch__item___0 :
  match_exception -> (pattern * FStar_Tactics_NamedView.term)) =
  fun projectee -> match projectee with | SimpleMismatch _0 -> _0
let (uu___is_NonLinearMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NonLinearMismatch _0 -> true | uu___ -> false
let (__proj__NonLinearMismatch__item___0 :
  match_exception ->
    (varname * FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term))
  = fun projectee -> match projectee with | NonLinearMismatch _0 -> _0
let (uu___is_UnsupportedTermInPattern : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnsupportedTermInPattern _0 -> true
    | uu___ -> false
let (__proj__UnsupportedTermInPattern__item___0 :
  match_exception -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | UnsupportedTermInPattern _0 -> _0
let (uu___is_IncorrectTypeInAbsPatBinder : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | IncorrectTypeInAbsPatBinder _0 -> true
    | uu___ -> false
let (__proj__IncorrectTypeInAbsPatBinder__item___0 :
  match_exception -> FStarC_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | IncorrectTypeInAbsPatBinder _0 -> _0
let (term_head :
  FStar_Tactics_NamedView.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ps ->
      let x = FStar_Tactics_NamedView.inspect t ps in
      match x with
      | FStar_Tactics_NamedView.Tv_Var bv -> "Tv_Var"
      | FStar_Tactics_NamedView.Tv_BVar fv -> "Tv_BVar"
      | FStar_Tactics_NamedView.Tv_FVar fv -> "Tv_FVar"
      | FStar_Tactics_NamedView.Tv_UInst (uu___, uu___1) -> "Tv_UInst"
      | FStar_Tactics_NamedView.Tv_App (f, x1) -> "Tv_App"
      | FStar_Tactics_NamedView.Tv_Abs (x1, t1) -> "Tv_Abs"
      | FStar_Tactics_NamedView.Tv_Arrow (x1, t1) -> "Tv_Arrow"
      | FStar_Tactics_NamedView.Tv_Type uu___ -> "Tv_Type"
      | FStar_Tactics_NamedView.Tv_Refine (x1, t1) -> "Tv_Refine"
      | FStar_Tactics_NamedView.Tv_Const cst -> "Tv_Const"
      | FStar_Tactics_NamedView.Tv_Uvar (i, t1) -> "Tv_Uvar"
      | FStar_Tactics_NamedView.Tv_Let (r, attrs, b, t1, t2) -> "Tv_Let"
      | FStar_Tactics_NamedView.Tv_Match (t1, uu___, branches) -> "Tv_Match"
      | FStar_Tactics_NamedView.Tv_AscribedT (uu___, uu___1, uu___2, uu___3)
          -> "Tv_AscribedT"
      | FStar_Tactics_NamedView.Tv_AscribedC (uu___, uu___1, uu___2, uu___3)
          -> "Tv_AscribedC"
      | FStar_Tactics_NamedView.Tv_Unknown -> "Tv_Unknown"
      | FStar_Tactics_NamedView.Tv_Unsupp -> "Tv_Unsupp"
let (string_of_match_exception :
  match_exception -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun uu___ ->
       match uu___ with
       | NameMismatch (qn1, qn2) ->
           Obj.magic
             (Obj.repr
                (fun uu___1 ->
                   Prims.strcat "Match failure (name mismatch): expecting "
                     (Prims.strcat qn1 (Prims.strcat ", found " qn2))))
       | SimpleMismatch (pat, tm) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x =
                     let x1 =
                       let x2 =
                         FStarC_Tactics_V2_Builtins.term_to_string tm ps in
                       Prims.strcat ", got " x2 in
                     Prims.strcat (desc_of_pattern pat) x1 in
                   Prims.strcat "Match failure (sort mismatch): expecting " x))
       | NonLinearMismatch (nm, t1, t2) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x =
                     let x1 =
                       let x2 =
                         let x3 =
                           FStarC_Tactics_V2_Builtins.term_to_string t1 ps in
                         let x4 =
                           let x5 =
                             FStarC_Tactics_V2_Builtins.term_to_string t2 ps in
                           Prims.strcat " and " x5 in
                         Prims.strcat x3 x4 in
                       Prims.strcat " needs to match both " x2 in
                     Prims.strcat nm x1 in
                   Prims.strcat
                     "Match failure (nonlinear mismatch): variable " x))
       | UnsupportedTermInPattern tm ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x =
                     let x1 = FStarC_Tactics_V2_Builtins.term_to_string tm ps in
                     let x2 =
                       let x3 =
                         let x4 = term_head tm ps in Prims.strcat x4 ")" in
                       Prims.strcat " (" x3 in
                     Prims.strcat x1 x2 in
                   Prims.strcat
                     "Match failure (unsupported term in pattern): " x))
       | IncorrectTypeInAbsPatBinder typ ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x =
                     let x1 =
                       FStarC_Tactics_V2_Builtins.term_to_string typ ps in
                     Prims.strcat x1
                       " (use one of ``var``, ``hyp \226\128\166``, or ``goal \226\128\166``)" in
                   Prims.strcat "Incorrect type in pattern-matching binder: "
                     x))) uu___
type 'a match_res =
  | Success of 'a 
  | Failure of match_exception 
let uu___is_Success : 'a . 'a match_res -> Prims.bool =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 : 'a . 'a match_res -> 'a =
  fun projectee -> match projectee with | Success _0 -> _0
let uu___is_Failure : 'a . 'a match_res -> Prims.bool =
  fun projectee -> match projectee with | Failure _0 -> true | uu___ -> false
let __proj__Failure__item___0 : 'a . 'a match_res -> match_exception =
  fun projectee -> match projectee with | Failure _0 -> _0
let return : 'a . 'a -> 'a match_res = fun x -> Success x
let op_let_Question :
  'a 'b .
    'a match_res ->
      ('a -> ('b match_res, unit) FStar_Tactics_Effect.tac_repr) ->
        ('b match_res, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun g ->
           match f with
           | Success aa -> Obj.magic (Obj.repr (g aa))
           | Failure ex -> Obj.magic (Obj.repr (fun uu___ -> Failure ex)))
        uu___1 uu___
let raise : 'a . match_exception -> 'a match_res = fun ex -> Failure ex
let lift_exn_tac :
  'a 'b .
    ('a -> 'b match_res) -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun aa ->
           match f aa with
           | Success bb -> Obj.magic (Obj.repr (fun uu___ -> bb))
           | Failure ex ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = string_of_match_exception ex ps in
                       FStar_Tactics_V1_Derived.fail x ps))) uu___1 uu___
let lift_exn_tactic :
  'a 'b .
    ('a -> 'b match_res) -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun aa ->
           match f aa with
           | Success bb -> Obj.magic (Obj.repr (fun uu___ -> bb))
           | Failure ex ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = string_of_match_exception ex ps in
                       FStar_Tactics_V1_Derived.fail x ps))) uu___1 uu___
type bindings = (varname * FStar_Tactics_NamedView.term) Prims.list
let (string_of_bindings :
  bindings -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun bindings1 ->
    fun ps ->
      let x =
        FStar_Tactics_Util.map
          (fun uu___ ->
             match uu___ with
             | (nm, tm) ->
                 (fun ps1 ->
                    let x1 =
                      let x2 =
                        let x3 =
                          FStarC_Tactics_V2_Builtins.term_to_string tm ps1 in
                        Prims.strcat ": " x3 in
                      Prims.strcat nm x2 in
                    Prims.strcat ">> " x1)) bindings1 ps in
      FStar_String.concat "\n" x
let rec (interp_pattern_aux :
  pattern ->
    bindings ->
      FStar_Tactics_NamedView.term ->
        (bindings match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun cur_bindings ->
      fun tm ->
        fun ps ->
          let x v =
            fun cur_bindings1 ->
              fun tm1 ->
                match FStar_List_Tot_Base.assoc v cur_bindings1 with
                | FStar_Pervasives_Native.Some tm' ->
                    if FStar_Reflection_TermEq_Simple.term_eq tm1 tm'
                    then return cur_bindings1
                    else raise (NonLinearMismatch (v, tm1, tm'))
                | FStar_Pervasives_Native.None ->
                    return ((v, tm1) :: cur_bindings1) in
          let x1 qn1 =
            fun cur_bindings1 ->
              fun tm1 ->
                fun ps1 ->
                  let x2 = FStar_Tactics_NamedView.inspect tm1 ps1 in
                  match x2 with
                  | FStar_Tactics_NamedView.Tv_UInst (fv, uu___) ->
                      if (FStar_Reflection_V2_Derived.fv_to_string fv) = qn1
                      then return cur_bindings1
                      else
                        raise
                          (NameMismatch
                             (qn1,
                               (FStar_Reflection_V2_Derived.fv_to_string fv)))
                  | FStar_Tactics_NamedView.Tv_FVar fv ->
                      if (FStar_Reflection_V2_Derived.fv_to_string fv) = qn1
                      then return cur_bindings1
                      else
                        raise
                          (NameMismatch
                             (qn1,
                               (FStar_Reflection_V2_Derived.fv_to_string fv)))
                  | uu___ -> raise (SimpleMismatch (pat, tm1)) in
          let x2 cur_bindings1 =
            fun tm1 ->
              fun ps1 ->
                let x3 = FStar_Tactics_NamedView.inspect tm1 ps1 in
                match x3 with
                | FStar_Tactics_NamedView.Tv_Type uu___ ->
                    return cur_bindings1
                | uu___ -> raise (SimpleMismatch (pat, tm1)) in
          let x3 p_hd =
            fun p_arg ->
              fun cur_bindings1 ->
                fun tm1 ->
                  fun ps1 ->
                    let x4 = FStar_Tactics_NamedView.inspect tm1 ps1 in
                    match x4 with
                    | FStar_Tactics_NamedView.Tv_App (hd, (arg, uu___)) ->
                        let x5 = interp_pattern_aux p_hd cur_bindings1 hd ps1 in
                        op_let_Question x5
                          (fun with_hd ->
                             fun ps2 ->
                               let x6 =
                                 interp_pattern_aux p_arg with_hd arg ps2 in
                               op_let_Question x6
                                 (fun uu___1 ->
                                    (fun with_arg ->
                                       Obj.magic
                                         (fun uu___1 -> return with_arg))
                                      uu___1) ps2) ps1
                    | uu___ -> raise (SimpleMismatch (pat, tm1)) in
          match pat with
          | PVar var -> x var cur_bindings tm
          | PQn qn1 -> x1 qn1 cur_bindings tm ps
          | PType -> x2 cur_bindings tm ps
          | PApp (p_hd, p_arg) -> x3 p_hd p_arg cur_bindings tm ps
let (interp_pattern :
  pattern ->
    FStar_Tactics_NamedView.term ->
      (bindings match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun tm ->
      fun ps ->
        let x = interp_pattern_aux pat [] tm ps in
        op_let_Question x
          (fun uu___ ->
             (fun rev_bindings ->
                Obj.magic
                  (fun uu___ -> return (FStar_List_Tot_Base.rev rev_bindings)))
               uu___) ps
let (match_term :
  pattern ->
    FStar_Tactics_NamedView.term ->
      (bindings, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun tm ->
      fun ps ->
        let x =
          let x1 = FStar_Tactics_V2_Derived.norm_term [] tm ps in
          interp_pattern pat x1 ps in
        match x with
        | Success bb -> bb
        | Failure ex ->
            let x1 = string_of_match_exception ex ps in
            FStar_Tactics_V1_Derived.fail x1 ps
let debug : 'uuuuu . 'uuuuu -> (unit, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ -> (fun msg -> Obj.magic (fun uu___ -> ())) uu___
type absvar = FStar_Tactics_NamedView.binding
type hypothesis = FStar_Tactics_NamedView.binding
type matching_problem =
  {
  mp_vars: varname Prims.list ;
  mp_hyps: (varname * pattern) Prims.list ;
  mp_goal: pattern FStar_Pervasives_Native.option }
let (__proj__Mkmatching_problem__item__mp_vars :
  matching_problem -> varname Prims.list) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_vars
let (__proj__Mkmatching_problem__item__mp_hyps :
  matching_problem -> (varname * pattern) Prims.list) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_hyps
let (__proj__Mkmatching_problem__item__mp_goal :
  matching_problem -> pattern FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_goal
let (string_of_matching_problem : matching_problem -> Prims.string) =
  fun mp ->
    let vars = FStar_String.concat ", " mp.mp_vars in
    let hyps =
      FStar_String.concat "\n        "
        (FStar_List_Tot_Base.map
           (fun uu___ ->
              match uu___ with
              | (nm, pat) ->
                  Prims.strcat nm (Prims.strcat ": " (string_of_pattern pat)))
           mp.mp_hyps) in
    let goal =
      match mp.mp_goal with
      | FStar_Pervasives_Native.None -> "_"
      | FStar_Pervasives_Native.Some pat -> string_of_pattern pat in
    Prims.strcat "\n{ vars: "
      (Prims.strcat vars
         (Prims.strcat "\n"
            (Prims.strcat "  hyps: "
               (Prims.strcat hyps
                  (Prims.strcat "\n"
                     (Prims.strcat "  goal: " (Prims.strcat goal " }")))))))
type matching_solution =
  {
  ms_vars: (varname * FStar_Tactics_NamedView.term) Prims.list ;
  ms_hyps: (varname * hypothesis) Prims.list }
let (__proj__Mkmatching_solution__item__ms_vars :
  matching_solution -> (varname * FStar_Tactics_NamedView.term) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_vars
let (__proj__Mkmatching_solution__item__ms_hyps :
  matching_solution -> (varname * hypothesis) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_hyps
let (string_of_matching_solution :
  matching_solution -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun ms ->
    fun ps ->
      let x =
        let x1 =
          FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (varname1, tm) ->
                   (fun ps1 ->
                      let x2 =
                        let x3 =
                          FStarC_Tactics_V2_Builtins.term_to_string tm ps1 in
                        Prims.strcat ": " x3 in
                      Prims.strcat varname1 x2)) ms.ms_vars ps in
        FStar_String.concat "\n            " x1 in
      let x1 =
        let x2 =
          FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (nm, binding) ->
                   (fun ps1 ->
                      let x3 =
                        let x4 =
                          FStar_Tactics_V2_Derived.binding_to_string binding
                            ps1 in
                        Prims.strcat ": " x4 in
                      Prims.strcat nm x3)) ms.ms_hyps ps in
        FStar_String.concat "\n        " x2 in
      Prims.strcat "\n{ vars: "
        (Prims.strcat x
           (Prims.strcat "\n"
              (Prims.strcat "  hyps: " (Prims.strcat x1 " }"))))
let assoc_varname_fail :
  'b .
    varname ->
      (varname * 'b) Prims.list -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun key ->
         fun ls ->
           match FStar_List_Tot_Base.assoc key ls with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V2_Derived.fail
                       (Prims.strcat "Not found: " key)))
           | FStar_Pervasives_Native.Some x ->
               Obj.magic (Obj.repr (fun uu___ -> x))) uu___1 uu___
let ms_locate_hyp :
  'a .
    matching_solution ->
      varname -> (hypothesis, unit) FStar_Tactics_Effect.tac_repr
  = fun solution -> fun name -> assoc_varname_fail name solution.ms_hyps
let ms_locate_var :
  'a .
    matching_solution -> varname -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun solution ->
    fun name ->
      fun ps ->
        let x = assoc_varname_fail name solution.ms_vars ps in
        FStarC_Tactics_V2_Builtins.unquote x ps
let ms_locate_unit :
  'uuuuu 'uuuuu1 'a .
    'uuuuu -> 'uuuuu1 -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun _solution -> fun _binder_name -> Obj.magic (fun uu___ -> ()))
        uu___1 uu___
let rec solve_mp_for_single_hyp :
  'a .
    varname ->
      pattern ->
        hypothesis Prims.list ->
          (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
            matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun name ->
    fun pat ->
      fun hypotheses ->
        fun body ->
          fun part_sol ->
            match hypotheses with
            | [] -> FStar_Tactics_V2_Derived.fail "No matching hypothesis"
            | h::hs ->
                FStar_Tactics_V2_Derived.or_else
                  (fun uu___ ->
                     fun ps ->
                       let x =
                         interp_pattern_aux pat part_sol.ms_vars
                           (FStar_Tactics_V2_Derived.type_of_binding h) ps in
                       match x with
                       | Failure ex ->
                           let x1 =
                             let x2 = string_of_match_exception ex ps in
                             Prims.strcat "Failed to match hyp: " x2 in
                           FStar_Tactics_V2_Derived.fail x1 ps
                       | Success bindings1 ->
                           let x1 = (name, h) :: (part_sol.ms_hyps) in
                           body { ms_vars = bindings1; ms_hyps = x1 } ps)
                  (fun uu___ ->
                     solve_mp_for_single_hyp name pat hs body part_sol)
let rec solve_mp_for_hyps :
  'a .
    (varname * pattern) Prims.list ->
      hypothesis Prims.list ->
        (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
          matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun mp_hyps ->
    fun hypotheses ->
      fun body ->
        fun partial_solution ->
          match mp_hyps with
          | [] -> body partial_solution
          | (name, pat)::pats ->
              solve_mp_for_single_hyp name pat hypotheses
                (solve_mp_for_hyps pats hypotheses body) partial_solution
let solve_mp :
  'a .
    matching_problem ->
      hypothesis Prims.list ->
        FStar_Tactics_NamedView.term ->
          (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
            ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun problem ->
    fun hypotheses ->
      fun goal ->
        fun body ->
          fun ps ->
            let x =
              match problem.mp_goal with
              | FStar_Pervasives_Native.None ->
                  { ms_vars = []; ms_hyps = [] }
              | FStar_Pervasives_Native.Some pat ->
                  let x1 = interp_pattern pat goal ps in
                  (match x1 with
                   | Failure ex ->
                       let x2 =
                         let x3 = string_of_match_exception ex ps in
                         Prims.strcat "Failed to match goal: " x3 in
                       FStar_Tactics_V2_Derived.fail x2 ps
                   | Success bindings1 ->
                       { ms_vars = bindings1; ms_hyps = [] }) in
            solve_mp_for_hyps problem.mp_hyps hypotheses body x ps
let (name_of_namedv :
  FStar_Tactics_NamedView.namedv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    FStarC_Tactics_Unseal.unseal
      (FStar_Tactics_NamedView.inspect_namedv x).FStarC_Reflection_V2_Data.ppname
let rec (pattern_of_term_ex :
  FStarC_Reflection_Types.term ->
    (pattern match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    fun ps ->
      let x = FStar_Tactics_NamedView.inspect tm ps in
      match x with
      | FStar_Tactics_NamedView.Tv_Var bv ->
          let x1 = let x2 = name_of_namedv bv ps in PVar x2 in return x1
      | FStar_Tactics_NamedView.Tv_FVar fv ->
          return (PQn (FStar_Reflection_V2_Derived.fv_to_string fv))
      | FStar_Tactics_NamedView.Tv_UInst (fv, uu___) ->
          return (PQn (FStar_Reflection_V2_Derived.fv_to_string fv))
      | FStar_Tactics_NamedView.Tv_Type uu___ -> return PType
      | FStar_Tactics_NamedView.Tv_App (f, (x1, uu___)) ->
          let x2 = pattern_of_term_ex f ps in
          op_let_Question x2
            (fun fpat ->
               fun ps1 ->
                 let x3 = pattern_of_term_ex x1 ps1 in
                 op_let_Question x3
                   (fun uu___1 ->
                      (fun xpat ->
                         Obj.magic (fun uu___1 -> return (PApp (fpat, xpat))))
                        uu___1) ps1) ps
      | uu___ -> raise (UnsupportedTermInPattern tm)
let (beta_reduce :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun tm -> FStar_Tactics_V2_Derived.norm_term [] tm
let (pattern_of_term :
  FStarC_Reflection_Types.term ->
    (pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    fun ps ->
      let x = pattern_of_term_ex tm ps in
      match x with
      | Success bb -> bb
      | Failure ex ->
          let x1 = string_of_match_exception ex ps in
          FStar_Tactics_V1_Derived.fail x1 ps
type 'a hyp = FStar_Tactics_NamedView.binding
type 'a pm_goal = unit
let (hyp_qn : Prims.string) = "FStar.Tactics.PatternMatching.hyp"
let (goal_qn : Prims.string) = "FStar.Tactics.PatternMatching.pm_goal"
type abspat_binder_kind =
  | ABKVar of FStarC_Reflection_Types.typ 
  | ABKHyp 
  | ABKGoal 
let (uu___is_ABKVar : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKVar _0 -> true | uu___ -> false
let (__proj__ABKVar__item___0 :
  abspat_binder_kind -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | ABKVar _0 -> _0
let (uu___is_ABKHyp : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKHyp -> true | uu___ -> false
let (uu___is_ABKGoal : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKGoal -> true | uu___ -> false
let (string_of_abspat_binder_kind : abspat_binder_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ABKVar uu___1 -> "varname"
    | ABKHyp -> "hyp"
    | ABKGoal -> "goal"
type abspat_argspec = {
  asa_name: absvar ;
  asa_kind: abspat_binder_kind }
let (__proj__Mkabspat_argspec__item__asa_name : abspat_argspec -> absvar) =
  fun projectee -> match projectee with | { asa_name; asa_kind;_} -> asa_name
let (__proj__Mkabspat_argspec__item__asa_kind :
  abspat_argspec -> abspat_binder_kind) =
  fun projectee -> match projectee with | { asa_name; asa_kind;_} -> asa_kind
type abspat_continuation =
  (abspat_argspec Prims.list * FStar_Tactics_NamedView.term)
let (type_of_named_binder :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.term) =
  fun nb -> nb.FStar_Tactics_NamedView.sort
let (classify_abspat_binder :
  FStar_Tactics_NamedView.binder ->
    ((abspat_binder_kind * FStar_Tactics_NamedView.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun ps ->
      let x = "v" in
      let x1 = PApp ((PQn hyp_qn), (PVar x)) in
      let x2 = PApp ((PQn goal_qn), (PVar x)) in
      let x3 = type_of_named_binder b in
      let x4 = interp_pattern x1 x3 ps in
      match x4 with
      | Success ((uu___, hyp_typ)::[]) -> (ABKHyp, hyp_typ)
      | Success uu___ ->
          FStar_Tactics_V2_Derived.fail
            "classifiy_abspat_binder: impossible (1)" ps
      | Failure uu___ ->
          let x5 = interp_pattern x2 x3 ps in
          (match x5 with
           | Success ((uu___1, goal_typ)::[]) -> (ABKGoal, goal_typ)
           | Success uu___1 ->
               FStar_Tactics_V2_Derived.fail
                 "classifiy_abspat_binder: impossible (2)" ps
           | Failure uu___1 -> ((ABKVar x3), x3))
let rec (binders_and_body_of_abs :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binder Prims.list *
       FStar_Tactics_NamedView.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    fun ps ->
      let x = FStar_Tactics_NamedView.inspect tm ps in
      match x with
      | FStar_Tactics_NamedView.Tv_Abs (binder, tm1) ->
          let x1 = binders_and_body_of_abs tm1 ps in
          (match x1 with | (binders, body) -> ((binder :: binders), body))
      | uu___ -> ([], tm)
let (cleanup_abspat :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Derived.norm_term [] t
let (name_of_named_binder :
  FStar_Tactics_NamedView.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun nb -> FStarC_Tactics_Unseal.unseal nb.FStar_Tactics_NamedView.ppname
let (matching_problem_of_abs :
  FStar_Tactics_NamedView.term ->
    ((matching_problem * abspat_continuation), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    fun ps ->
      let x = let x1 = cleanup_abspat tm ps in binders_and_body_of_abs x1 ps in
      match x with
      | (binders, body) ->
          ((let x2 =
              let x3 =
                let x4 =
                  FStar_Tactics_Util.map (fun b -> name_of_named_binder b)
                    binders ps in
                FStar_String.concat ", " x4 in
              Prims.strcat "Got binders: " x3 in
            debug x2 ps);
           (let x2 =
              FStar_Tactics_Util.map
                (fun binder ->
                   fun ps1 ->
                     let x3 = name_of_named_binder binder ps1 in
                     (let x5 =
                        let x6 =
                          let x7 =
                            let x8 =
                              FStarC_Tactics_V2_Builtins.term_to_string
                                (type_of_named_binder binder) ps1 in
                            Prims.strcat "; type is " x8 in
                          Prims.strcat x3 x7 in
                        Prims.strcat "Got binder: " x6 in
                      debug x5 ps1);
                     (let x5 = classify_abspat_binder binder ps1 in
                      match x5 with
                      | (binder_kind, typ) -> (binder, x3, binder_kind, typ)))
                binders ps in
            let x3 =
              FStar_Tactics_Util.fold_left
                (fun problem ->
                   fun uu___ ->
                     match uu___ with
                     | (binder, bv_name, binder_kind, typ) ->
                         (fun ps1 ->
                            (let x5 =
                               let x6 =
                                 let x7 = name_of_named_binder binder ps1 in
                                 let x8 =
                                   let x9 =
                                     let x10 =
                                       let x11 =
                                         FStarC_Tactics_V2_Builtins.term_to_string
                                           typ ps1 in
                                       Prims.strcat ", with type " x11 in
                                     Prims.strcat
                                       (string_of_abspat_binder_kind
                                          binder_kind) x10 in
                                   Prims.strcat ", classified as " x9 in
                                 Prims.strcat x7 x8 in
                               Prims.strcat "Compiling binder " x6 in
                             debug x5 ps1);
                            (match binder_kind with
                             | ABKVar uu___1 ->
                                 {
                                   mp_vars = (bv_name :: (problem.mp_vars));
                                   mp_hyps = (problem.mp_hyps);
                                   mp_goal = (problem.mp_goal)
                                 }
                             | ABKHyp ->
                                 let x5 =
                                   let x6 =
                                     let x7 = pattern_of_term typ ps1 in
                                     (bv_name, x7) in
                                   x6 :: (problem.mp_hyps) in
                                 {
                                   mp_vars = (problem.mp_vars);
                                   mp_hyps = x5;
                                   mp_goal = (problem.mp_goal)
                                 }
                             | ABKGoal ->
                                 let x5 =
                                   let x6 = pattern_of_term typ ps1 in
                                   FStar_Pervasives_Native.Some x6 in
                                 {
                                   mp_vars = (problem.mp_vars);
                                   mp_hyps = (problem.mp_hyps);
                                   mp_goal = x5
                                 })))
                {
                  mp_vars = [];
                  mp_hyps = [];
                  mp_goal = FStar_Pervasives_Native.None
                } x2 ps in
            let x4 =
              let x5 uu___ =
                (fun xx ->
                   Obj.magic
                     (fun uu___ ->
                        match xx with
                        | (binder, xx1, binder_kind, yy) ->
                            {
                              asa_name =
                                (FStar_Tactics_NamedView.binder_to_binding
                                   binder);
                              asa_kind = binder_kind
                            })) uu___ in
              let x6 = FStar_Tactics_Util.map x5 x2 ps in (x6, tm) in
            let x5 =
              {
                mp_vars = (FStar_List_Tot_Base.rev x3.mp_vars);
                mp_hyps = (FStar_List_Tot_Base.rev x3.mp_hyps);
                mp_goal = (x3.mp_goal)
              } in
            debug
              (Prims.strcat "Got matching problem: "
                 (string_of_matching_problem x5)) ps;
            (x5, x4)))
let (arg_type_of_binder_kind :
  abspat_binder_kind ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun binder_kind ->
       Obj.magic
         (fun uu___ ->
            match binder_kind with
            | ABKVar typ -> typ
            | ABKHyp ->
                FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "NamedView"; "binder"]))
            | ABKGoal ->
                FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"]))))
      uu___
let (locate_fn_of_binder_kind :
  abspat_binder_kind -> FStarC_Reflection_Types.term) =
  fun binder_kind ->
    match binder_kind with
    | ABKVar uu___ ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_var"]))
    | ABKHyp ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_hyp"]))
    | ABKGoal ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_unit"]))
let (abspat_arg_of_abspat_argspec :
  FStarC_Reflection_Types.term ->
    abspat_argspec ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun solution_term ->
    fun argspec ->
      fun ps ->
        let x = locate_fn_of_binder_kind argspec.asa_kind in
        let x1 =
          let x2 =
            let x3 =
              let x4 =
                FStarC_Tactics_Unseal.unseal
                  (argspec.asa_name).FStarC_Reflection_V2_Data.ppname3 ps in
              FStarC_Reflection_V2_Data.C_String x4 in
            FStar_Tactics_NamedView.Tv_Const x3 in
          FStar_Tactics_NamedView.pack x2 in
        let x2 =
          let x3 =
            let x4 = arg_type_of_binder_kind argspec.asa_kind ps in
            (x4, FStarC_Reflection_V2_Data.Q_Explicit) in
          [x3;
          (solution_term, FStarC_Reflection_V2_Data.Q_Explicit);
          (x1, FStarC_Reflection_V2_Data.Q_Explicit)] in
        FStar_Reflection_V2_Derived.mk_app x x2
let rec (hoist_and_apply :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStarC_Reflection_V2_Data.argv Prims.list ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun head ->
           fun arg_terms ->
             fun hoisted_args ->
               match arg_terms with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (fun uu___ ->
                           FStar_Reflection_V2_Derived.mk_app head
                             (FStar_List_Tot_Base.rev hoisted_args)))
               | arg_term::rest ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x = FStar_List_Tot_Base.length hoisted_args in
                           let x1 =
                             let x2 = FStarC_Tactics_V2_Builtins.fresh () ps in
                             {
                               FStar_Tactics_NamedView.uniq = x2;
                               FStar_Tactics_NamedView.ppname =
                                 (FStar_Sealed.seal
                                    (Prims.strcat "x" (Prims.string_of_int x)));
                               FStar_Tactics_NamedView.sort =
                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                    FStarC_Reflection_V2_Data.Tv_Unknown);
                               FStar_Tactics_NamedView.qual =
                                 FStarC_Reflection_V2_Data.Q_Explicit;
                               FStar_Tactics_NamedView.attrs = []
                             } in
                           let x2 =
                             let x3 =
                               hoist_and_apply head rest
                                 (((FStar_Tactics_NamedView.pack
                                      (FStar_Tactics_NamedView.Tv_Var
                                         (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                            x1))),
                                    FStarC_Reflection_V2_Data.Q_Explicit) ::
                                 hoisted_args) ps in
                             FStar_Tactics_NamedView.Tv_Let
                               (false, [], x1, arg_term, x3) in
                           FStar_Tactics_NamedView.pack x2))) uu___2 uu___1
          uu___
let (specialize_abspat_continuation' :
  abspat_continuation ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun continuation ->
    fun solution_term ->
      fun ps ->
        let x argspec = abspat_arg_of_abspat_argspec solution_term argspec in
        let x1 = continuation in
        match x1 with
        | (argspecs, body) ->
            let x2 = FStar_Tactics_Util.map x argspecs ps in
            hoist_and_apply body x2 [] ps
let (specialize_abspat_continuation :
  abspat_continuation ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun continuation ->
    fun ps ->
      let x =
        FStar_Tactics_V2_Derived.fresh_binder
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_FVar
                (FStarC_Reflection_V2_Builtins.pack_fv
                   ["FStar";
                   "Tactics";
                   "PatternMatching";
                   "matching_solution"]))) ps in
      let x1 =
        FStar_Tactics_NamedView.pack
          (FStar_Tactics_NamedView.Tv_Var
             (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv x)) in
      let x2 = specialize_abspat_continuation' continuation x1 ps in
      let x3 =
        FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_Abs (x, x2)) in
      (let x5 =
         let x6 = FStarC_Tactics_V2_Builtins.term_to_string x3 ps in
         Prims.strcat "Specialized into " x6 in
       debug x5 ps);
      (let x5 = beta_reduce x3 ps in
       (let x7 =
          let x8 = FStarC_Tactics_V2_Builtins.term_to_string x5 ps in
          Prims.strcat "\226\128\166 which reduces to " x8 in
        debug x7 ps);
       x3)
let interp_abspat_continuation :
  'a .
    abspat_continuation ->
      (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr, 
        unit) FStar_Tactics_Effect.tac_repr
  =
  fun continuation ->
    fun ps ->
      let x = specialize_abspat_continuation continuation ps in
      FStarC_Tactics_V2_Builtins.unquote x ps
let interp_abspat :
  'a .
    'a ->
      ((matching_problem * abspat_continuation), unit)
        FStar_Tactics_Effect.tac_repr
  =
  fun abspat ->
    fun ps ->
      let x =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      matching_problem_of_abs x ps
let match_abspat :
  'b 'a .
    'a ->
      (abspat_continuation ->
         (matching_solution -> ('b, unit) FStar_Tactics_Effect.tac_repr,
           unit) FStar_Tactics_Effect.tac_repr)
        -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun abspat ->
    fun k ->
      fun ps ->
        let x = FStar_Tactics_V2_Derived.cur_goal () ps in
        let x1 =
          let x2 = FStar_Tactics_V2_Derived.cur_env () ps in
          FStarC_Reflection_V2_Builtins.vars_of_env x2 in
        let x2 = interp_abspat abspat ps in
        match x2 with
        | (problem, continuation) ->
            let x3 = k continuation ps in solve_mp problem x1 x x3 ps
let inspect_abspat_problem :
  'a . 'a -> (matching_problem, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    fun ps ->
      let x = interp_abspat abspat ps in FStar_Pervasives_Native.fst x
let inspect_abspat_solution :
  'a . 'a -> (matching_solution, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    match_abspat abspat
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (fun uu___1 ->
                 fun solution -> Obj.magic (fun uu___2 -> solution))) uu___)
let tpair :
  'a 'b .
    'a ->
      ('b -> (('a * 'b), unit) FStar_Tactics_Effect.tac_repr, unit)
        FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun x ->
       Obj.magic (fun uu___ -> fun y -> Obj.magic (fun uu___1 -> (x, y))))
      uu___
let gpm : 'b 'a . 'a -> unit -> ('b, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    fun uu___ ->
      fun ps ->
        let x = match_abspat abspat tpair ps in
        match x with
        | (continuation, solution) ->
            let x1 = interp_abspat_continuation continuation ps in
            x1 solution ps
let pm : 'b 'a . 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat -> match_abspat abspat interp_abspat_continuation
let fetch_eq_side' :
  'a . unit -> (FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term)
  =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (gpm
            (fun left ->
               fun right ->
                 fun g ->
                   fun ps ->
                     let x =
                       Obj.magic
                         (failwith
                            "Cannot evaluate open quotation at runtime") in
                     let x1 =
                       Obj.magic
                         (failwith
                            "Cannot evaluate open quotation at runtime") in
                     (x, x1)) ())) uu___
