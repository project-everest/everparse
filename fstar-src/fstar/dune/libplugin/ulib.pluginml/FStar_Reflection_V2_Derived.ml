open Fstarcompiler
open Prims
let (type_of_binder :
  Fstarcompiler.FStarC_Reflection_Types.binder ->
    Fstarcompiler.FStarC_Reflection_Types.typ)
  =
  fun b ->
    (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_binder b).Fstarcompiler.FStarC_Reflection_V2_Data.sort2
let rec (inspect_ln_unascribe :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_V2_Data.term_view)
  =
  fun t ->
    match Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_ln t with
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_AscribedT
        (t', uu___, uu___1, uu___2) -> inspect_ln_unascribe t'
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_AscribedC
        (t', uu___, uu___1, uu___2) -> inspect_ln_unascribe t'
    | tv -> tv
let (compare_bv :
  Fstarcompiler.FStarC_Reflection_Types.bv ->
    Fstarcompiler.FStarC_Reflection_Types.bv -> FStar_Order.order)
  =
  fun v1 ->
    fun v2 ->
      FStar_Order.compare_int
        (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_bv v1).Fstarcompiler.FStarC_Reflection_V2_Data.index
        (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_bv v2).Fstarcompiler.FStarC_Reflection_V2_Data.index
let (compare_namedv :
  Fstarcompiler.FStarC_Reflection_Types.namedv ->
    Fstarcompiler.FStarC_Reflection_Types.namedv -> FStar_Order.order)
  =
  fun v1 ->
    fun v2 ->
      FStar_Order.compare_int
        (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_namedv v1).Fstarcompiler.FStarC_Reflection_V2_Data.uniq
        (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_namedv v2).Fstarcompiler.FStarC_Reflection_V2_Data.uniq
let (shift :
  Prims.int ->
    Fstarcompiler.FStarC_Syntax_Syntax.subst_elt ->
      Fstarcompiler.FStarC_Syntax_Syntax.subst_elt)
  =
  fun n ->
    fun s ->
      match s with
      | Fstarcompiler.FStarC_Syntax_Syntax.DB (i, t) ->
          Fstarcompiler.FStarC_Syntax_Syntax.DB ((i + n), t)
      | Fstarcompiler.FStarC_Syntax_Syntax.DT (i, t) ->
          Fstarcompiler.FStarC_Syntax_Syntax.DT ((i + n), t)
      | Fstarcompiler.FStarC_Syntax_Syntax.UN (i, t) ->
          Fstarcompiler.FStarC_Syntax_Syntax.UN ((i + n), t)
      | Fstarcompiler.FStarC_Syntax_Syntax.NM (x, i) ->
          Fstarcompiler.FStarC_Syntax_Syntax.NM (x, (i + n))
      | Fstarcompiler.FStarC_Syntax_Syntax.UD (x, i) ->
          Fstarcompiler.FStarC_Syntax_Syntax.UD (x, (i + n))
      | Fstarcompiler.FStarC_Syntax_Syntax.NT (uu___, uu___1) -> s
let (shift_subst :
  Prims.int ->
    Fstarcompiler.FStarC_Syntax_Syntax.subst_elt Prims.list ->
      Fstarcompiler.FStarC_Syntax_Syntax.subst_elt Prims.list)
  = fun n -> fun s -> FStar_List_Tot_Base.map (shift n) s
let (subst1 :
  Fstarcompiler.FStarC_Reflection_Types.namedv ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun n ->
    fun t1 ->
      fun t2 ->
        Fstarcompiler.FStarC_Reflection_V2_Builtins.subst_term
          [Fstarcompiler.FStarC_Syntax_Syntax.NT (n, t1)] t2
let (mk_binder :
  Prims.string ->
    Fstarcompiler.FStarC_Reflection_Types.typ ->
      Fstarcompiler.FStarC_Reflection_V2_Data.simple_binder)
  =
  fun nm ->
    fun sort ->
      let bv =
        {
          Fstarcompiler.FStarC_Reflection_V2_Data.sort2 = sort;
          Fstarcompiler.FStarC_Reflection_V2_Data.qual =
            Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit;
          Fstarcompiler.FStarC_Reflection_V2_Data.attrs = [];
          Fstarcompiler.FStarC_Reflection_V2_Data.ppname2 =
            (FStar_Sealed.seal nm)
        } in
      Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_binder bv
let (mk_implicit_binder :
  Prims.string ->
    Fstarcompiler.FStarC_Reflection_Types.typ ->
      Fstarcompiler.FStarC_Reflection_Types.binder)
  =
  fun nm ->
    fun sort ->
      Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_binder
        {
          Fstarcompiler.FStarC_Reflection_V2_Data.sort2 = sort;
          Fstarcompiler.FStarC_Reflection_V2_Data.qual =
            Fstarcompiler.FStarC_Reflection_V2_Data.Q_Implicit;
          Fstarcompiler.FStarC_Reflection_V2_Data.attrs = [];
          Fstarcompiler.FStarC_Reflection_V2_Data.ppname2 =
            (FStar_Sealed.seal nm)
        }
let (push_binding :
  Fstarcompiler.FStarC_Reflection_Types.env ->
    Fstarcompiler.FStarC_Reflection_V2_Data.binding ->
      Fstarcompiler.FStarC_Reflection_Types.env)
  =
  fun e ->
    fun b ->
      let nv =
        Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_namedv
          {
            Fstarcompiler.FStarC_Reflection_V2_Data.uniq =
              (b.Fstarcompiler.FStarC_Reflection_V2_Data.uniq1);
            Fstarcompiler.FStarC_Reflection_V2_Data.sort =
              (FStar_Sealed.seal
                 b.Fstarcompiler.FStarC_Reflection_V2_Data.sort3);
            Fstarcompiler.FStarC_Reflection_V2_Data.ppname =
              (b.Fstarcompiler.FStarC_Reflection_V2_Data.ppname3)
          } in
      Fstarcompiler.FStarC_Reflection_V2_Builtins.push_namedv e nv
let rec (flatten_name :
  Fstarcompiler.FStarC_Reflection_Types.name -> Prims.string) =
  fun ns ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let rec (mk_app :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_V2_Data.argv Prims.list ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
               (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App (t, x))) xs
let (mk_e_app :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term Prims.list ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      let e t1 = (t1, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit) in
      mk_app t (FStar_List_Tot_Base.map e args)
let (u_unk : Fstarcompiler.FStarC_Reflection_Types.universe) =
  Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_universe
    Fstarcompiler.FStarC_Reflection_V2_Data.Uv_Unk
let rec (mk_tot_arr_ln :
  Fstarcompiler.FStarC_Reflection_Types.binder Prims.list ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> cod
      | b::bs1 ->
          Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
            (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Arrow
               (b,
                 (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_comp
                    (Fstarcompiler.FStarC_Reflection_V2_Data.C_Total
                       (mk_tot_arr_ln bs1 cod)))))
let rec (mk_arr_ln :
  Fstarcompiler.FStarC_Reflection_Types.binder Prims.list ->
    Fstarcompiler.FStarC_Reflection_Types.comp ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun bs ->
    fun cod ->
      match bs with
      | b::[] ->
          Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
            (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
            (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Arrow
               (b,
                 (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_comp
                    (Fstarcompiler.FStarC_Reflection_V2_Data.C_Total
                       (mk_arr_ln bs1 cod)))))
let (fv_to_string : Fstarcompiler.FStarC_Reflection_Types.fv -> Prims.string)
  =
  fun fv ->
    Fstarcompiler.FStarC_Reflection_V2_Builtins.implode_qn
      (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_fv fv)
let (mk_stringlit :
  Prims.string -> Fstarcompiler.FStarC_Reflection_Types.term) =
  fun s ->
    Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
      (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Const
         (Fstarcompiler.FStarC_Reflection_V2_Data.C_String s))
let (mk_strcat :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      mk_e_app
        (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
           (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
              (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                 ["Prims"; "strcat"]))) [t1; t2]
let (mk_cons :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun h ->
    fun t ->
      mk_e_app
        (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
           (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
              (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                 FStar_Reflection_Const.cons_qn))) [h; t]
let (mk_cons_t :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun ty ->
    fun h ->
      fun t ->
        mk_app
          (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
             (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                   FStar_Reflection_Const.cons_qn)))
          [(ty, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Implicit);
          (h, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit);
          (t, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)]
let rec (mk_list :
  Fstarcompiler.FStarC_Reflection_Types.term Prims.list ->
    Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun ts ->
    match ts with
    | [] ->
        Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
          (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
             (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.nil_qn))
    | t::ts1 -> mk_cons t (mk_list ts1)
let (mktuple_n :
  Fstarcompiler.FStarC_Reflection_Types.term Prims.list ->
    Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun ts ->
    match FStar_List_Tot_Base.length ts with
    | uu___ when uu___ = Prims.int_zero ->
        Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
          (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Const
             Fstarcompiler.FStarC_Reflection_V2_Data.C_Unit)
    | uu___ when uu___ = Prims.int_one ->
        let uu___1 = ts in (match uu___1 with | x::[] -> x)
    | n ->
        let qn =
          match n with
          | uu___ when uu___ = (Prims.of_int (2)) ->
              FStar_Reflection_Const.mktuple2_qn
          | uu___ when uu___ = (Prims.of_int (3)) ->
              FStar_Reflection_Const.mktuple3_qn
          | uu___ when uu___ = (Prims.of_int (4)) ->
              FStar_Reflection_Const.mktuple4_qn
          | uu___ when uu___ = (Prims.of_int (5)) ->
              FStar_Reflection_Const.mktuple5_qn
          | uu___ when uu___ = (Prims.of_int (6)) ->
              FStar_Reflection_Const.mktuple6_qn
          | uu___ when uu___ = (Prims.of_int (7)) ->
              FStar_Reflection_Const.mktuple7_qn
          | uu___ when uu___ = (Prims.of_int (8)) ->
              FStar_Reflection_Const.mktuple8_qn in
        mk_e_app
          (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
             (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv qn))) ts
let (destruct_tuple :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term Prims.list
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Collect.collect_app_ln t in
    match uu___ with
    | (head, args) ->
        (match Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_ln head
         with
         | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar fv ->
             if
               FStar_List_Tot_Base.mem
                 (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_fv fv)
                 [FStar_Reflection_Const.mktuple2_qn;
                 FStar_Reflection_Const.mktuple3_qn;
                 FStar_Reflection_Const.mktuple4_qn;
                 FStar_Reflection_Const.mktuple5_qn;
                 FStar_Reflection_Const.mktuple6_qn;
                 FStar_Reflection_Const.mktuple7_qn;
                 FStar_Reflection_Const.mktuple8_qn]
             then
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.concatMap
                    (fun uu___1 ->
                       match uu___1 with
                       | (t1, q) ->
                           (match q with
                            | Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit
                                -> [t1]
                            | uu___2 -> [])) args)
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
let (mkpair :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.term)
  = fun t1 -> fun t2 -> mktuple_n [t1; t2]
let rec (head :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun t ->
    match Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_ln t with
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Match (t1, uu___, uu___1) ->
        head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Let
        (uu___, uu___1, uu___2, t1, uu___3) -> head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Abs (uu___, t1) -> head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Refine (uu___, t1) ->
        head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App (t1, uu___) -> head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_AscribedT
        (t1, uu___, uu___1, uu___2) -> head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_AscribedC
        (t1, uu___, uu___1, uu___2) -> head t1
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Unknown -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Const uu___ -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Type uu___ -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Var uu___ -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_BVar uu___ -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar uu___ -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Arrow (uu___, uu___1) -> t
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Unsupp -> t
let (is_fvar :
  Fstarcompiler.FStarC_Reflection_Types.term -> Prims.string -> Prims.bool) =
  fun t ->
    fun nm ->
      match inspect_ln_unascribe t with
      | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar fv ->
          (Fstarcompiler.FStarC_Reflection_V2_Builtins.implode_qn
             (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = nm
      | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
          (Fstarcompiler.FStarC_Reflection_V2_Builtins.implode_qn
             (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = nm
      | uu___ -> false
let rec (is_any_fvar :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Prims.string Prims.list -> Prims.bool)
  =
  fun t ->
    fun nms ->
      match nms with
      | [] -> false
      | v::vs -> (is_fvar t v) || (is_any_fvar t vs)
let (is_uvar : Fstarcompiler.FStarC_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_ln (head t)
    with
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> true
    | uu___ -> false
let (binder_set_qual :
  Fstarcompiler.FStarC_Reflection_V2_Data.aqualv ->
    Fstarcompiler.FStarC_Reflection_Types.binder ->
      Fstarcompiler.FStarC_Reflection_Types.binder)
  =
  fun q ->
    fun b ->
      let bview =
        Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_binder b in
      Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_binder
        {
          Fstarcompiler.FStarC_Reflection_V2_Data.sort2 =
            (bview.Fstarcompiler.FStarC_Reflection_V2_Data.sort2);
          Fstarcompiler.FStarC_Reflection_V2_Data.qual = q;
          Fstarcompiler.FStarC_Reflection_V2_Data.attrs =
            (bview.Fstarcompiler.FStarC_Reflection_V2_Data.attrs);
          Fstarcompiler.FStarC_Reflection_V2_Data.ppname2 =
            (bview.Fstarcompiler.FStarC_Reflection_V2_Data.ppname2)
        }
let (add_check_with :
  Fstarcompiler.FStarC_VConfig.vconfig ->
    Fstarcompiler.FStarC_Reflection_Types.sigelt ->
      Fstarcompiler.FStarC_Reflection_Types.sigelt)
  =
  fun vcfg ->
    fun se ->
      let attrs = Fstarcompiler.FStarC_Reflection_V2_Builtins.sigelt_attrs se in
      let vcfg_t =
        Fstarcompiler.FStarC_Reflection_V2_Builtins.embed_vconfig vcfg in
      let t =
        Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
          (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
             ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                 (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "Stubs"; "VConfig"; "check_with"]))),
               (vcfg_t, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit))) in
      Fstarcompiler.FStarC_Reflection_V2_Builtins.set_sigelt_attrs (t ::
        attrs) se
let (un_uinst :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun t ->
    match Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_ln t with
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
        Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
          (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar fv)
    | uu___ -> t
let rec (is_name_imp :
  Fstarcompiler.FStarC_Reflection_Types.name ->
    Fstarcompiler.FStarC_Reflection_Types.term -> Prims.bool)
  =
  fun nm ->
    fun t ->
      match inspect_ln_unascribe t with
      | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar fv ->
          if (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_fv fv) = nm
          then true
          else false
      | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
          if (Fstarcompiler.FStarC_Reflection_V2_Builtins.inspect_fv fv) = nm
          then true
          else false
      | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
          (l, (uu___, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Implicit)) ->
          is_name_imp nm l
      | uu___ -> false
let (unsquash_term :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match inspect_ln_unascribe t with
    | Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
        (l, (r, Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)) ->
        if is_name_imp FStar_Reflection_Const.squash_qn l
        then FStar_Pervasives_Native.Some r
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (maybe_unsquash_term :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term)
  =
  fun t ->
    match unsquash_term t with
    | FStar_Pervasives_Native.Some t' -> t'
    | FStar_Pervasives_Native.None -> t