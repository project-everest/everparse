open Fstarcompiler
open Prims
let (run_all : unit -> unit) =
  fun uu___ ->
    let b = FStarC_Syntax_Syntax.mk_binder in
    let id = FStarC_Tests_Pars.pars "fun x -> x" in
    let apply = FStarC_Tests_Pars.pars "fun f x -> f x" in
    let twice = FStarC_Tests_Pars.pars "fun f x -> f (f x)" in
    let tt = FStarC_Tests_Pars.pars "fun x y -> x" in
    let ff = FStarC_Tests_Pars.pars "fun x y -> y" in
    let z = FStarC_Tests_Pars.pars "fun f x -> x" in
    let one = FStarC_Tests_Pars.pars "fun f x -> f x" in
    let two = FStarC_Tests_Pars.pars "fun f x -> f (f x)" in
    let succ = FStarC_Tests_Pars.pars "fun n f x -> f (n f x)" in
    let pred =
      FStarC_Tests_Pars.pars
        "fun n f x -> n (fun g h -> h (g f)) (fun y -> x) (fun y -> y)" in
    let mul = FStarC_Tests_Pars.pars "fun m n f -> m (n f)" in
    let rec encode n =
      if n = Prims.int_zero
      then z
      else
        (let uu___2 = let uu___3 = encode (n - Prims.int_one) in [uu___3] in
         FStarC_Tests_Util.app succ uu___2) in
    let minus m = fun n -> FStarC_Tests_Util.app n [pred; m] in
    let let_ x =
      fun e ->
        fun e' ->
          let uu___1 =
            let uu___2 = let uu___3 = b x in [uu___3] in
            FStarC_Syntax_Util.abs uu___2 e' FStar_Pervasives_Native.None in
          FStarC_Tests_Util.app uu___1 [e] in
    let mk_let x =
      fun e ->
        fun e' ->
          let e'1 =
            FStarC_Syntax_Subst.subst
              [FStarC_Syntax_Syntax.NM (x, Prims.int_zero)] e' in
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_let
               {
                 FStarC_Syntax_Syntax.lbs =
                   (false,
                     [{
                        FStarC_Syntax_Syntax.lbname =
                          (Fstarcompiler.FStar_Pervasives.Inl x);
                        FStarC_Syntax_Syntax.lbunivs = [];
                        FStarC_Syntax_Syntax.lbtyp = FStarC_Syntax_Syntax.tun;
                        FStarC_Syntax_Syntax.lbeff =
                          FStarC_Parser_Const.effect_Tot_lid;
                        FStarC_Syntax_Syntax.lbdef = e;
                        FStarC_Syntax_Syntax.lbattrs = [];
                        FStarC_Syntax_Syntax.lbpos =
                          FStarC_Range_Type.dummyRange
                      }]);
                 FStarC_Syntax_Syntax.body1 = e'1
               }) FStarC_Range_Type.dummyRange in
    let lid x =
      FStarC_Ident.lid_of_path ["Test"; x] FStarC_Range_Type.dummyRange in
    let znat_l =
      let uu___1 = lid "Z" in
      FStarC_Syntax_Syntax.lid_as_fv uu___1
        (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
    let snat_l =
      let uu___1 = lid "S" in
      FStarC_Syntax_Syntax.lid_as_fv uu___1
        (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
    let tm_fv fv =
      FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_fvar fv)
        FStarC_Range_Type.dummyRange in
    let znat = tm_fv znat_l in
    let snat s =
      let uu___1 =
        let uu___2 =
          let uu___3 = tm_fv snat_l in
          let uu___4 = let uu___5 = FStarC_Syntax_Syntax.as_arg s in [uu___5] in
          {
            FStarC_Syntax_Syntax.hd = uu___3;
            FStarC_Syntax_Syntax.args = uu___4
          } in
        FStarC_Syntax_Syntax.Tm_app uu___2 in
      FStarC_Syntax_Syntax.mk uu___1 FStarC_Range_Type.dummyRange in
    let pat p = FStarC_Syntax_Syntax.withinfo p FStarC_Range_Type.dummyRange in
    let snat_type =
      let uu___1 =
        let uu___2 = lid "snat" in
        FStarC_Syntax_Syntax.lid_as_fv uu___2 FStar_Pervasives_Native.None in
      tm_fv uu___1 in
    let mk_match h =
      fun branches ->
        let branches1 = FStarC_List.map FStarC_Syntax_Util.branch branches in
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_match
             {
               FStarC_Syntax_Syntax.scrutinee = h;
               FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
               FStarC_Syntax_Syntax.brs = branches1;
               FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
             }) FStarC_Range_Type.dummyRange in
    let pred_nat s =
      let zbranch =
        let uu___1 =
          pat
            (FStarC_Syntax_Syntax.Pat_cons
               (znat_l, FStar_Pervasives_Native.None, [])) in
        (uu___1, FStar_Pervasives_Native.None, znat) in
      let sbranch =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    pat (FStarC_Syntax_Syntax.Pat_var FStarC_Tests_Util.x) in
                  (uu___6, false) in
                [uu___5] in
              (snat_l, FStar_Pervasives_Native.None, uu___4) in
            FStarC_Syntax_Syntax.Pat_cons uu___3 in
          pat uu___2 in
        let uu___2 =
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_bvar
               {
                 FStarC_Syntax_Syntax.ppname =
                   (FStarC_Tests_Util.x.FStarC_Syntax_Syntax.ppname);
                 FStarC_Syntax_Syntax.index = Prims.int_zero;
                 FStarC_Syntax_Syntax.sort =
                   (FStarC_Tests_Util.x.FStarC_Syntax_Syntax.sort)
               }) FStarC_Range_Type.dummyRange in
        (uu___1, FStar_Pervasives_Native.None, uu___2) in
      mk_match s [zbranch; sbranch] in
    let minus_nat t1 =
      fun t2 ->
        let minus1 = FStarC_Tests_Util.m in
        let x =
          {
            FStarC_Syntax_Syntax.ppname =
              (FStarC_Tests_Util.x.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index =
              (FStarC_Tests_Util.x.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = snat_type
          } in
        let y =
          {
            FStarC_Syntax_Syntax.ppname =
              (FStarC_Tests_Util.y.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index =
              (FStarC_Tests_Util.y.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = snat_type
          } in
        let zbranch =
          let uu___1 =
            pat
              (FStarC_Syntax_Syntax.Pat_cons
                 (znat_l, FStar_Pervasives_Native.None, [])) in
          let uu___2 = FStarC_Tests_Util.nm x in
          (uu___1, FStar_Pervasives_Native.None, uu___2) in
        let sbranch =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      pat (FStarC_Syntax_Syntax.Pat_var FStarC_Tests_Util.n) in
                    (uu___6, false) in
                  [uu___5] in
                (snat_l, FStar_Pervasives_Native.None, uu___4) in
              FStarC_Syntax_Syntax.Pat_cons uu___3 in
            pat uu___2 in
          let uu___2 =
            let uu___3 = FStarC_Tests_Util.nm minus1 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_Tests_Util.nm x in pred_nat uu___6 in
              let uu___6 =
                let uu___7 = FStarC_Tests_Util.nm FStarC_Tests_Util.n in
                [uu___7] in
              uu___5 :: uu___6 in
            FStarC_Tests_Util.app uu___3 uu___4 in
          (uu___1, FStar_Pervasives_Native.None, uu___2) in
        let lb =
          let uu___1 =
            FStarC_Ident.lid_of_path ["Pure"] FStarC_Range_Type.dummyRange in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = b x in
                let uu___6 = let uu___7 = b y in [uu___7] in uu___5 :: uu___6 in
              let uu___5 =
                let uu___6 = FStarC_Tests_Util.nm y in
                mk_match uu___6 [zbranch; sbranch] in
              FStarC_Syntax_Util.abs uu___4 uu___5
                FStar_Pervasives_Native.None in
            FStarC_Syntax_Subst.subst
              [FStarC_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu___3 in
          {
            FStarC_Syntax_Syntax.lbname =
              (Fstarcompiler.FStar_Pervasives.Inl minus1);
            FStarC_Syntax_Syntax.lbunivs = [];
            FStarC_Syntax_Syntax.lbtyp = FStarC_Syntax_Syntax.tun;
            FStarC_Syntax_Syntax.lbeff = uu___1;
            FStarC_Syntax_Syntax.lbdef = uu___2;
            FStarC_Syntax_Syntax.lbattrs = [];
            FStarC_Syntax_Syntax.lbpos = FStarC_Range_Type.dummyRange
          } in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Tests_Util.nm minus1 in
                FStarC_Tests_Util.app uu___5 [t1; t2] in
              FStarC_Syntax_Subst.subst
                [FStarC_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu___4 in
            {
              FStarC_Syntax_Syntax.lbs = (true, [lb]);
              FStarC_Syntax_Syntax.body1 = uu___3
            } in
          FStarC_Syntax_Syntax.Tm_let uu___2 in
        FStarC_Syntax_Syntax.mk uu___1 FStarC_Range_Type.dummyRange in
    let encode_nat n =
      let rec aux out =
        fun n1 ->
          if n1 = Prims.int_zero
          then out
          else (let uu___2 = snat out in aux uu___2 (n1 - Prims.int_one)) in
      aux znat n in
    let default_tests =
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let recons (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | hd::tl -> hd::tl";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "type snat = | Z | S : snat -> snat";
      FStarC_Tests_Pars.pars_and_tc_fragment "type tb = | T | F";
      FStarC_Tests_Pars.pars_and_tc_fragment "type rb = | A1 | A2 | A3";
      FStarC_Tests_Pars.pars_and_tc_fragment "type hb = | H : tb -> hb";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let select (i:tb) (x:'a) (y:'a) : Tot 'a = match i with | T -> x | F -> y";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let select_int3 (i:int) (x:'a) (y:'a) (z:'a) : Tot 'a = match i with | 0 -> x | 1 -> y | _ -> z";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let select_bool (b:bool) (x:'a) (y:'a) : Tot 'a = if b then x else y";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let select_string3 (s:string) (x:'a) (y:'a) (z:'a) : Tot 'a = match s with | \"abc\" -> x | \"def\" -> y | _ -> z";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let recons_m (x:list tb) = match x with | [] -> []  | hd::tl -> hd::tl";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let rec copy_tb_list_2 (x:list tb) : Tot (list tb) = match x with | [] -> []  | [hd] -> [hd]\n                                            | hd1::hd2::tl -> hd1::hd2::copy_tb_list_2 tl";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let rec copy_list_2 (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | [hd] -> [hd]\n                                            | hd1::hd2::tl -> hd1::hd2::copy_list_2 tl";
      FStarC_Tests_Pars.pars_and_tc_fragment "let (x1:int{x1>3}) = 6";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let (x2:int{x2+1>3 /\\ not (x2-5>0)}) = 2";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let my_plus (x:int) (y:int) = x + y";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let (x3:int{forall (a:nat). a > x2}) = 7";
      FStarC_Tests_Pars.pars_and_tc_fragment "let idd (x: 'a) = x";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "let revtb (x: tb) = match x with | T -> F | F -> T";
      FStarC_Tests_Pars.pars_and_tc_fragment "let id_tb (x: tb) = x";
      FStarC_Tests_Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x";
      FStarC_Tests_Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x";
      FStarC_Tests_Pars.pars_and_tc_fragment "let id_list_m (x: list tb) = x";
      (let uu___26 =
         let uu___27 =
           let uu___28 =
             let uu___29 =
               let uu___30 =
                 let uu___31 = FStarC_Tests_Util.nm FStarC_Tests_Util.n in
                 [uu___31] in
               id :: uu___30 in
             one :: uu___29 in
           FStarC_Tests_Util.app apply uu___28 in
         let uu___28 = FStarC_Tests_Util.nm FStarC_Tests_Util.n in
         (Prims.int_zero, uu___27, uu___28) in
       let uu___27 =
         let uu___28 =
           let uu___29 =
             let uu___30 =
               let uu___31 = FStarC_Tests_Util.nm FStarC_Tests_Util.x in
               [uu___31] in
             FStarC_Tests_Util.app id uu___30 in
           let uu___30 = FStarC_Tests_Util.nm FStarC_Tests_Util.x in
           (Prims.int_one, uu___29, uu___30) in
         let uu___29 =
           let uu___30 =
             let uu___31 =
               let uu___32 =
                 let uu___33 =
                   let uu___34 = FStarC_Tests_Util.nm FStarC_Tests_Util.n in
                   let uu___35 =
                     let uu___36 = FStarC_Tests_Util.nm FStarC_Tests_Util.m in
                     [uu___36] in
                   uu___34 :: uu___35 in
                 tt :: uu___33 in
               FStarC_Tests_Util.app apply uu___32 in
             let uu___32 = FStarC_Tests_Util.nm FStarC_Tests_Util.n in
             (Prims.int_one, uu___31, uu___32) in
           let uu___31 =
             let uu___32 =
               let uu___33 =
                 let uu___34 =
                   let uu___35 =
                     let uu___36 = FStarC_Tests_Util.nm FStarC_Tests_Util.n in
                     let uu___37 =
                       let uu___38 = FStarC_Tests_Util.nm FStarC_Tests_Util.m in
                       [uu___38] in
                     uu___36 :: uu___37 in
                   ff :: uu___35 in
                 FStarC_Tests_Util.app apply uu___34 in
               let uu___34 = FStarC_Tests_Util.nm FStarC_Tests_Util.m in
               ((Prims.of_int (2)), uu___33, uu___34) in
             let uu___33 =
               let uu___34 =
                 let uu___35 =
                   let uu___36 =
                     let uu___37 =
                       let uu___38 =
                         let uu___39 =
                           let uu___40 =
                             let uu___41 =
                               let uu___42 =
                                 let uu___43 =
                                   FStarC_Tests_Util.nm FStarC_Tests_Util.n in
                                 let uu___44 =
                                   let uu___45 =
                                     FStarC_Tests_Util.nm FStarC_Tests_Util.m in
                                   [uu___45] in
                                 uu___43 :: uu___44 in
                               ff :: uu___42 in
                             apply :: uu___41 in
                           apply :: uu___40 in
                         apply :: uu___39 in
                       apply :: uu___38 in
                     apply :: uu___37 in
                   FStarC_Tests_Util.app apply uu___36 in
                 let uu___36 = FStarC_Tests_Util.nm FStarC_Tests_Util.m in
                 ((Prims.of_int (3)), uu___35, uu___36) in
               let uu___35 =
                 let uu___36 =
                   let uu___37 =
                     let uu___38 =
                       let uu___39 =
                         let uu___40 =
                           let uu___41 =
                             FStarC_Tests_Util.nm FStarC_Tests_Util.n in
                           let uu___42 =
                             let uu___43 =
                               FStarC_Tests_Util.nm FStarC_Tests_Util.m in
                             [uu___43] in
                           uu___41 :: uu___42 in
                         ff :: uu___40 in
                       apply :: uu___39 in
                     FStarC_Tests_Util.app twice uu___38 in
                   let uu___38 = FStarC_Tests_Util.nm FStarC_Tests_Util.m in
                   ((Prims.of_int (4)), uu___37, uu___38) in
                 let uu___37 =
                   let uu___38 =
                     let uu___39 = minus one z in
                     ((Prims.of_int (5)), uu___39, one) in
                   let uu___39 =
                     let uu___40 =
                       let uu___41 = FStarC_Tests_Util.app pred [one] in
                       ((Prims.of_int (6)), uu___41, z) in
                     let uu___41 =
                       let uu___42 =
                         let uu___43 = minus one one in
                         ((Prims.of_int (7)), uu___43, z) in
                       let uu___43 =
                         let uu___44 =
                           let uu___45 = FStarC_Tests_Util.app mul [one; one] in
                           ((Prims.of_int (8)), uu___45, one) in
                         let uu___45 =
                           let uu___46 =
                             let uu___47 =
                               FStarC_Tests_Util.app mul [two; one] in
                             ((Prims.of_int (9)), uu___47, two) in
                           let uu___47 =
                             let uu___48 =
                               let uu___49 =
                                 let uu___50 =
                                   let uu___51 =
                                     FStarC_Tests_Util.app succ [one] in
                                   [uu___51; one] in
                                 FStarC_Tests_Util.app mul uu___50 in
                               ((Prims.of_int (10)), uu___49, two) in
                             let uu___49 =
                               let uu___50 =
                                 let uu___51 =
                                   let uu___52 = encode (Prims.of_int (10)) in
                                   let uu___53 = encode (Prims.of_int (10)) in
                                   minus uu___52 uu___53 in
                                 ((Prims.of_int (11)), uu___51, z) in
                               let uu___51 =
                                 let uu___52 =
                                   let uu___53 =
                                     let uu___54 =
                                       encode (Prims.of_int (100)) in
                                     let uu___55 =
                                       encode (Prims.of_int (100)) in
                                     minus uu___54 uu___55 in
                                   ((Prims.of_int (12)), uu___53, z) in
                                 let uu___53 =
                                   let uu___54 =
                                     let uu___55 =
                                       let uu___56 =
                                         encode (Prims.of_int (100)) in
                                       let uu___57 =
                                         let uu___58 =
                                           FStarC_Tests_Util.nm
                                             FStarC_Tests_Util.x in
                                         let uu___59 =
                                           FStarC_Tests_Util.nm
                                             FStarC_Tests_Util.x in
                                         minus uu___58 uu___59 in
                                       let_ FStarC_Tests_Util.x uu___56
                                         uu___57 in
                                     ((Prims.of_int (13)), uu___55, z) in
                                   let uu___55 =
                                     let uu___56 =
                                       let uu___57 =
                                         let uu___58 =
                                           FStarC_Tests_Util.app succ [one] in
                                         let uu___59 =
                                           let uu___60 =
                                             let uu___61 =
                                               let uu___62 =
                                                 FStarC_Tests_Util.nm
                                                   FStarC_Tests_Util.x in
                                               let uu___63 =
                                                 let uu___64 =
                                                   FStarC_Tests_Util.nm
                                                     FStarC_Tests_Util.x in
                                                 [uu___64] in
                                               uu___62 :: uu___63 in
                                             FStarC_Tests_Util.app mul
                                               uu___61 in
                                           let uu___61 =
                                             let uu___62 =
                                               let uu___63 =
                                                 let uu___64 =
                                                   FStarC_Tests_Util.nm
                                                     FStarC_Tests_Util.y in
                                                 let uu___65 =
                                                   let uu___66 =
                                                     FStarC_Tests_Util.nm
                                                       FStarC_Tests_Util.y in
                                                   [uu___66] in
                                                 uu___64 :: uu___65 in
                                               FStarC_Tests_Util.app mul
                                                 uu___63 in
                                             let uu___63 =
                                               let uu___64 =
                                                 FStarC_Tests_Util.nm
                                                   FStarC_Tests_Util.h in
                                               let uu___65 =
                                                 FStarC_Tests_Util.nm
                                                   FStarC_Tests_Util.h in
                                               minus uu___64 uu___65 in
                                             let_ FStarC_Tests_Util.h uu___62
                                               uu___63 in
                                           let_ FStarC_Tests_Util.y uu___60
                                             uu___61 in
                                         let_ FStarC_Tests_Util.x uu___58
                                           uu___59 in
                                       ((Prims.of_int (15)), uu___57, z) in
                                     let uu___57 =
                                       let uu___58 =
                                         let uu___59 =
                                           let uu___60 =
                                             FStarC_Tests_Util.app succ [one] in
                                           let uu___61 =
                                             let uu___62 =
                                               let uu___63 =
                                                 let uu___64 =
                                                   FStarC_Tests_Util.nm
                                                     FStarC_Tests_Util.x in
                                                 let uu___65 =
                                                   let uu___66 =
                                                     FStarC_Tests_Util.nm
                                                       FStarC_Tests_Util.x in
                                                   [uu___66] in
                                                 uu___64 :: uu___65 in
                                               FStarC_Tests_Util.app mul
                                                 uu___63 in
                                             let uu___63 =
                                               let uu___64 =
                                                 let uu___65 =
                                                   let uu___66 =
                                                     FStarC_Tests_Util.nm
                                                       FStarC_Tests_Util.y in
                                                   let uu___67 =
                                                     let uu___68 =
                                                       FStarC_Tests_Util.nm
                                                         FStarC_Tests_Util.y in
                                                     [uu___68] in
                                                   uu___66 :: uu___67 in
                                                 FStarC_Tests_Util.app mul
                                                   uu___65 in
                                               let uu___65 =
                                                 let uu___66 =
                                                   FStarC_Tests_Util.nm
                                                     FStarC_Tests_Util.h in
                                                 let uu___67 =
                                                   FStarC_Tests_Util.nm
                                                     FStarC_Tests_Util.h in
                                                 minus uu___66 uu___67 in
                                               mk_let FStarC_Tests_Util.h
                                                 uu___64 uu___65 in
                                             mk_let FStarC_Tests_Util.y
                                               uu___62 uu___63 in
                                           mk_let FStarC_Tests_Util.x uu___60
                                             uu___61 in
                                         ((Prims.of_int (16)), uu___59, z) in
                                       let uu___59 =
                                         let uu___60 =
                                           let uu___61 =
                                             let uu___62 =
                                               FStarC_Tests_Util.app succ
                                                 [one] in
                                             let uu___63 =
                                               let uu___64 =
                                                 let uu___65 =
                                                   let uu___66 =
                                                     FStarC_Tests_Util.nm
                                                       FStarC_Tests_Util.x in
                                                   let uu___67 =
                                                     let uu___68 =
                                                       FStarC_Tests_Util.nm
                                                         FStarC_Tests_Util.x in
                                                     [uu___68] in
                                                   uu___66 :: uu___67 in
                                                 FStarC_Tests_Util.app mul
                                                   uu___65 in
                                               let uu___65 =
                                                 let uu___66 =
                                                   let uu___67 =
                                                     let uu___68 =
                                                       FStarC_Tests_Util.nm
                                                         FStarC_Tests_Util.y in
                                                     let uu___69 =
                                                       let uu___70 =
                                                         FStarC_Tests_Util.nm
                                                           FStarC_Tests_Util.y in
                                                       [uu___70] in
                                                     uu___68 :: uu___69 in
                                                   FStarC_Tests_Util.app mul
                                                     uu___67 in
                                                 let uu___67 =
                                                   let uu___68 =
                                                     FStarC_Tests_Util.nm
                                                       FStarC_Tests_Util.h in
                                                   let uu___69 =
                                                     FStarC_Tests_Util.nm
                                                       FStarC_Tests_Util.h in
                                                   minus uu___68 uu___69 in
                                                 let_ FStarC_Tests_Util.h
                                                   uu___66 uu___67 in
                                               let_ FStarC_Tests_Util.y
                                                 uu___64 uu___65 in
                                             let_ FStarC_Tests_Util.x uu___62
                                               uu___63 in
                                           ((Prims.of_int (17)), uu___61, z) in
                                         let uu___61 =
                                           let uu___62 =
                                             let uu___63 =
                                               let uu___64 =
                                                 let uu___65 = snat znat in
                                                 snat uu___65 in
                                               pred_nat uu___64 in
                                             let uu___64 = snat znat in
                                             ((Prims.of_int (18)), uu___63,
                                               uu___64) in
                                           let uu___63 =
                                             let uu___64 =
                                               let uu___65 =
                                                 let uu___66 =
                                                   let uu___67 =
                                                     let uu___68 = snat znat in
                                                     snat uu___68 in
                                                   let uu___68 = snat znat in
                                                   minus_nat uu___67 uu___68 in
                                                 FStarC_Tests_Pars.tc_term
                                                   uu___66 in
                                               let uu___66 = snat znat in
                                               ((Prims.of_int (19)), uu___65,
                                                 uu___66) in
                                             let uu___65 =
                                               let uu___66 =
                                                 let uu___67 =
                                                   let uu___68 =
                                                     let uu___69 =
                                                       encode_nat
                                                         (Prims.of_int (10)) in
                                                     let uu___70 =
                                                       encode_nat
                                                         (Prims.of_int (10)) in
                                                     minus_nat uu___69
                                                       uu___70 in
                                                   FStarC_Tests_Pars.tc_term
                                                     uu___68 in
                                                 ((Prims.of_int (20)),
                                                   uu___67, znat) in
                                               let uu___67 =
                                                 let uu___68 =
                                                   let uu___69 =
                                                     let uu___70 =
                                                       let uu___71 =
                                                         encode_nat
                                                           (Prims.of_int (100)) in
                                                       let uu___72 =
                                                         encode_nat
                                                           (Prims.of_int (100)) in
                                                       minus_nat uu___71
                                                         uu___72 in
                                                     FStarC_Tests_Pars.tc_term
                                                       uu___70 in
                                                   ((Prims.of_int (21)),
                                                     uu___69, znat) in
                                                 let uu___69 =
                                                   let uu___70 =
                                                     let uu___71 =
                                                       FStarC_Tests_Pars.tc
                                                         "recons [0;1]" in
                                                     let uu___72 =
                                                       FStarC_Tests_Pars.tc
                                                         "[0;1]" in
                                                     ((Prims.of_int (24)),
                                                       uu___71, uu___72) in
                                                   let uu___71 =
                                                     let uu___72 =
                                                       let uu___73 =
                                                         FStarC_Tests_Pars.tc
                                                           "recons [false;true;false]" in
                                                       let uu___74 =
                                                         FStarC_Tests_Pars.tc
                                                           "[false;true;false]" in
                                                       ((Prims.of_int (241)),
                                                         uu___73, uu___74) in
                                                     let uu___73 =
                                                       let uu___74 =
                                                         let uu___75 =
                                                           FStarC_Tests_Pars.tc
                                                             "copy [0;1]" in
                                                         let uu___76 =
                                                           FStarC_Tests_Pars.tc
                                                             "[0;1]" in
                                                         ((Prims.of_int (25)),
                                                           uu___75, uu___76) in
                                                       let uu___75 =
                                                         let uu___76 =
                                                           let uu___77 =
                                                             FStarC_Tests_Pars.tc
                                                               "rev [0;1;2;3;4;5;6;7;8;9;10]" in
                                                           let uu___78 =
                                                             FStarC_Tests_Pars.tc
                                                               "[10;9;8;7;6;5;4;3;2;1;0]" in
                                                           ((Prims.of_int (26)),
                                                             uu___77,
                                                             uu___78) in
                                                         let uu___77 =
                                                           let uu___78 =
                                                             let uu___79 =
                                                               FStarC_Tests_Pars.tc
                                                                 "(fun x y z q -> z) T T F T" in
                                                             let uu___80 =
                                                               FStarC_Tests_Pars.tc
                                                                 "F" in
                                                             ((Prims.of_int (28)),
                                                               uu___79,
                                                               uu___80) in
                                                           let uu___79 =
                                                             let uu___80 =
                                                               let uu___81 =
                                                                 FStarC_Tests_Pars.tc
                                                                   "[T; F]" in
                                                               let uu___82 =
                                                                 FStarC_Tests_Pars.tc
                                                                   "[T; F]" in
                                                               ((Prims.of_int (29)),
                                                                 uu___81,
                                                                 uu___82) in
                                                             let uu___81 =
                                                               let uu___82 =
                                                                 let uu___83
                                                                   =
                                                                   FStarC_Tests_Pars.tc
                                                                    "id_tb T" in
                                                                 let uu___84
                                                                   =
                                                                   FStarC_Tests_Pars.tc
                                                                    "T" in
                                                                 ((Prims.of_int (31)),
                                                                   uu___83,
                                                                   uu___84) in
                                                               let uu___83 =
                                                                 let uu___84
                                                                   =
                                                                   let uu___85
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "(fun #a x -> x) #tb T" in
                                                                   let uu___86
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "T" in
                                                                   ((Prims.of_int (32)),
                                                                    uu___85,
                                                                    uu___86) in
                                                                 let uu___85
                                                                   =
                                                                   let uu___86
                                                                    =
                                                                    let uu___87
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "revtb T" in
                                                                    let uu___88
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "F" in
                                                                    ((Prims.of_int (33)),
                                                                    uu___87,
                                                                    uu___88) in
                                                                   let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    let uu___89
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "(fun x y -> x) T F" in
                                                                    let uu___90
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "T" in
                                                                    ((Prims.of_int (34)),
                                                                    uu___89,
                                                                    uu___90) in
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    let uu___91
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "fst_a T F" in
                                                                    let uu___92
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "T" in
                                                                    ((Prims.of_int (35)),
                                                                    uu___91,
                                                                    uu___92) in
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    let uu___93
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "idd T" in
                                                                    let uu___94
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "T" in
                                                                    ((Prims.of_int (36)),
                                                                    uu___93,
                                                                    uu___94) in
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "id_list [T]" in
                                                                    let uu___96
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[T]" in
                                                                    ((Prims.of_int (301)),
                                                                    uu___95,
                                                                    uu___96) in
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "id_list_m [T]" in
                                                                    let uu___98
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[T]" in
                                                                    ((Prims.of_int (3012)),
                                                                    uu___97,
                                                                    uu___98) in
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "recons_m [T; F]" in
                                                                    let uu___100
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[T; F]" in
                                                                    ((Prims.of_int (302)),
                                                                    uu___99,
                                                                    uu___100) in
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "select T A1 A3" in
                                                                    let uu___102
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "A1" in
                                                                    ((Prims.of_int (303)),
                                                                    uu___101,
                                                                    uu___102) in
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "select T 3 4" in
                                                                    let uu___104
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "3" in
                                                                    ((Prims.of_int (3031)),
                                                                    uu___103,
                                                                    uu___104) in
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    let uu___105
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "select_bool false 3 4" in
                                                                    let uu___106
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "4" in
                                                                    ((Prims.of_int (3032)),
                                                                    uu___105,
                                                                    uu___106) in
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "select_int3 1 7 8 9" in
                                                                    let uu___108
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "8" in
                                                                    ((Prims.of_int (3033)),
                                                                    uu___107,
                                                                    uu___108) in
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[5]" in
                                                                    let uu___110
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[5]" in
                                                                    ((Prims.of_int (3034)),
                                                                    uu___109,
                                                                    uu___110) in
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[\"abcd\"]" in
                                                                    let uu___112
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[\"abcd\"]" in
                                                                    ((Prims.of_int (3035)),
                                                                    uu___111,
                                                                    uu___112) in
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "select_string3 \"def\" 5 6 7" in
                                                                    let uu___114
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "6" in
                                                                    ((Prims.of_int (3036)),
                                                                    uu___113,
                                                                    uu___114) in
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "idd T" in
                                                                    let uu___116
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "T" in
                                                                    ((Prims.of_int (305)),
                                                                    uu___115,
                                                                    uu___116) in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    let uu___117
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "recons [T]" in
                                                                    let uu___118
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[T]" in
                                                                    ((Prims.of_int (306)),
                                                                    uu___117,
                                                                    uu___118) in
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]" in
                                                                    let uu___120
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (307)),
                                                                    uu___119,
                                                                    uu___120) in
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    let uu___121
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "copy_list_2    [T;F;T;F;T;F;F]" in
                                                                    let uu___122
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (308)),
                                                                    uu___121,
                                                                    uu___122) in
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "rev [T; F; F]" in
                                                                    let uu___124
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[F; F; T]" in
                                                                    ((Prims.of_int (304)),
                                                                    uu___123,
                                                                    uu___124) in
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    let uu___125
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "rev [[T]; [F; T]]" in
                                                                    let uu___126
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "[[F; T]; [T]]" in
                                                                    ((Prims.of_int (305)),
                                                                    uu___125,
                                                                    uu___126) in
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    let uu___127
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "x1" in
                                                                    let uu___128
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "6" in
                                                                    ((Prims.of_int (309)),
                                                                    uu___127,
                                                                    uu___128) in
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    let uu___129
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "x2" in
                                                                    let uu___130
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "2" in
                                                                    ((Prims.of_int (310)),
                                                                    uu___129,
                                                                    uu___130) in
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    let uu___131
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "7 + 3" in
                                                                    let uu___132
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "10" in
                                                                    ((Prims.of_int (401)),
                                                                    uu___131,
                                                                    uu___132) in
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    let uu___133
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "true && false" in
                                                                    let uu___134
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "false" in
                                                                    ((Prims.of_int (402)),
                                                                    uu___133,
                                                                    uu___134) in
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    let uu___135
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "3 = 5" in
                                                                    let uu___136
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "false" in
                                                                    ((Prims.of_int (403)),
                                                                    uu___135,
                                                                    uu___136) in
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    let uu___137
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "\"abc\" ^ \"def\"" in
                                                                    let uu___138
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "\"abcdef\"" in
                                                                    ((Prims.of_int (404)),
                                                                    uu___137,
                                                                    uu___138) in
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
                                                                    =
                                                                    let uu___139
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "(fun (x:list int) -> match x with | [] -> 0 | hd::tl -> 1) []" in
                                                                    let uu___140
                                                                    =
                                                                    FStarC_Tests_Pars.tc
                                                                    "0" in
                                                                    ((Prims.of_int (405)),
                                                                    uu___139,
                                                                    uu___140) in
                                                                    [uu___138] in
                                                                    uu___136
                                                                    ::
                                                                    uu___137 in
                                                                    uu___134
                                                                    ::
                                                                    uu___135 in
                                                                    uu___132
                                                                    ::
                                                                    uu___133 in
                                                                    uu___130
                                                                    ::
                                                                    uu___131 in
                                                                    uu___128
                                                                    ::
                                                                    uu___129 in
                                                                    uu___126
                                                                    ::
                                                                    uu___127 in
                                                                    uu___124
                                                                    ::
                                                                    uu___125 in
                                                                    uu___122
                                                                    ::
                                                                    uu___123 in
                                                                    uu___120
                                                                    ::
                                                                    uu___121 in
                                                                    uu___118
                                                                    ::
                                                                    uu___119 in
                                                                    uu___116
                                                                    ::
                                                                    uu___117 in
                                                                    uu___114
                                                                    ::
                                                                    uu___115 in
                                                                    uu___112
                                                                    ::
                                                                    uu___113 in
                                                                    uu___110
                                                                    ::
                                                                    uu___111 in
                                                                    uu___108
                                                                    ::
                                                                    uu___109 in
                                                                    uu___106
                                                                    ::
                                                                    uu___107 in
                                                                    uu___104
                                                                    ::
                                                                    uu___105 in
                                                                    uu___102
                                                                    ::
                                                                    uu___103 in
                                                                    uu___100
                                                                    ::
                                                                    uu___101 in
                                                                    uu___98
                                                                    ::
                                                                    uu___99 in
                                                                    uu___96
                                                                    ::
                                                                    uu___97 in
                                                                    uu___94
                                                                    ::
                                                                    uu___95 in
                                                                    uu___92
                                                                    ::
                                                                    uu___93 in
                                                                    uu___90
                                                                    ::
                                                                    uu___91 in
                                                                    uu___88
                                                                    ::
                                                                    uu___89 in
                                                                   uu___86 ::
                                                                    uu___87 in
                                                                 uu___84 ::
                                                                   uu___85 in
                                                               uu___82 ::
                                                                 uu___83 in
                                                             uu___80 ::
                                                               uu___81 in
                                                           uu___78 :: uu___79 in
                                                         uu___76 :: uu___77 in
                                                       uu___74 :: uu___75 in
                                                     uu___72 :: uu___73 in
                                                   uu___70 :: uu___71 in
                                                 uu___68 :: uu___69 in
                                               uu___66 :: uu___67 in
                                             uu___64 :: uu___65 in
                                           uu___62 :: uu___63 in
                                         uu___60 :: uu___61 in
                                       uu___58 :: uu___59 in
                                     uu___56 :: uu___57 in
                                   uu___54 :: uu___55 in
                                 uu___52 :: uu___53 in
                               uu___50 :: uu___51 in
                             uu___48 :: uu___49 in
                           uu___46 :: uu___47 in
                         uu___44 :: uu___45 in
                       uu___42 :: uu___43 in
                     uu___40 :: uu___41 in
                   uu___38 :: uu___39 in
                 uu___36 :: uu___37 in
               uu___34 :: uu___35 in
             uu___32 :: uu___33 in
           uu___30 :: uu___31 in
         uu___28 :: uu___29 in
       uu___26 :: uu___27) in
    let run_either i =
      fun r ->
        fun expected ->
          fun normalizer ->
            (let uu___2 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
             FStarC_Format.print1 "%s: ... \n\n" uu___2);
            (let tcenv = FStarC_Tests_Pars.init () in
             (let uu___3 = FStarC_Options.parse_cmd_line () in ());
             (let x = normalizer tcenv r in
              FStarC_Options.init ();
              FStarC_Options.set_option "print_universes"
                (FStarC_Options.Bool true);
              FStarC_Options.set_option "print_implicits"
                (FStarC_Options.Bool true);
              FStarC_Options.set_option "ugly" (FStarC_Options.Bool true);
              FStarC_Options.set_option "print_bound_var_types"
                (FStarC_Options.Bool true);
              (let uu___8 =
                 let uu___9 = FStarC_Syntax_Util.unascribe x in
                 FStarC_Tests_Util.term_eq uu___9 expected in
               FStarC_Tests_Util.always i uu___8))) in
    let run_whnf i =
      fun r ->
        fun expected ->
          let steps =
            [FStarC_TypeChecker_Env.Primops;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] in
          run_either i r expected
            (FStarC_TypeChecker_Normalize.normalize steps) in
    let run_interpreter i =
      fun r ->
        fun expected ->
          run_either i r expected
            (FStarC_TypeChecker_Normalize.normalize
               [FStarC_TypeChecker_Env.Beta;
               FStarC_TypeChecker_Env.UnfoldUntil
                 FStarC_Syntax_Syntax.delta_constant;
               FStarC_TypeChecker_Env.Primops]) in
    let run_nbe i =
      fun r ->
        fun expected ->
          run_either i r expected
            (FStarC_TypeChecker_NBE.normalize_for_unit_test
               [FStarC_TypeChecker_Env.UnfoldUntil
                  FStarC_Syntax_Syntax.delta_constant]) in
    let run_interpreter_with_time i =
      fun r ->
        fun expected ->
          let interp uu___1 = run_interpreter i r expected in
          let uu___1 =
            let uu___2 = FStarC_Util.return_execution_time interp in
            FStar_Pervasives_Native.snd uu___2 in
          (i, uu___1) in
    let run_whnf_with_time i =
      fun r ->
        fun expected ->
          let whnf uu___1 = run_whnf i r expected in
          let uu___1 =
            let uu___2 = FStarC_Util.return_execution_time whnf in
            FStar_Pervasives_Native.snd uu___2 in
          (i, uu___1) in
    let run_nbe_with_time i =
      fun r ->
        fun expected ->
          let nbe uu___1 = run_nbe i r expected in
          let uu___1 =
            let uu___2 = FStarC_Util.return_execution_time nbe in
            FStar_Pervasives_Native.snd uu___2 in
          (i, uu___1) in
    let run_tests tests =
      fun run ->
        let l =
          FStarC_List.map
            (fun uu___1 ->
               match uu___1 with | (no, test, res) -> run no test res) tests in
        l in
    let whnf_tests =
      FStarC_Tests_Pars.pars_and_tc_fragment "assume val def : Type0";
      FStarC_Tests_Pars.pars_and_tc_fragment "assume val pred : Type0";
      FStarC_Tests_Pars.pars_and_tc_fragment "let def0 (y:int) = def";
      FStarC_Tests_Pars.pars_and_tc_fragment
        "unfold let def1 (y:int) = x:def0 y { pred }";
      (let def_def1 = FStarC_Tests_Pars.tc "x:def0 17 { pred }" in
       let def_def1_unfolded = FStarC_Tests_Pars.tc "x:def { pred }" in
       let tests =
         let uu___5 =
           let uu___6 = FStarC_Tests_Pars.tc "def1 17" in
           ((Prims.of_int (601)), uu___6, def_def1) in
         [uu___5; ((Prims.of_int (602)), def_def1, def_def1_unfolded)] in
       tests) in
    let run_all_whnf uu___1 =
      FStarC_Format.print_string "Testing Normlizer WHNF\n";
      (let uu___3 = run_tests whnf_tests run_whnf in
       FStarC_Format.print_string "Normalizer WHNF ok\n") in
    let run_all_nbe uu___1 =
      FStarC_Format.print_string "Testing NBE\n";
      (let uu___3 = run_tests default_tests run_nbe in
       FStarC_Format.print_string "NBE ok\n") in
    let run_all_interpreter uu___1 =
      FStarC_Format.print_string "Testing the normalizer\n";
      (let uu___3 = run_tests default_tests run_interpreter in
       FStarC_Format.print_string "Normalizer ok\n") in
    let run_all_whnf_with_time uu___1 =
      FStarC_Format.print_string "Testing WHNF\n";
      (let l = run_tests whnf_tests run_whnf_with_time in
       FStarC_Format.print_string "WHNF ok\n"; l) in
    let run_all_nbe_with_time uu___1 =
      FStarC_Format.print_string "Testing NBE\n";
      (let l = run_tests default_tests run_nbe_with_time in
       FStarC_Format.print_string "NBE ok\n"; l) in
    let run_all_interpreter_with_time uu___1 =
      FStarC_Format.print_string "Testing the normalizer\n";
      (let l = run_tests default_tests run_interpreter_with_time in
       FStarC_Format.print_string "Normalizer ok\n"; l) in
    let run_both_with_time i =
      fun r ->
        fun expected ->
          let nbe uu___1 = run_nbe i r expected in
          let norm uu___1 = run_interpreter i r expected in
          FStarC_Util.measure_execution_time "nbe" nbe;
          FStarC_Format.print_string "\n";
          FStarC_Util.measure_execution_time "normalizer" norm;
          FStarC_Format.print_string "\n" in
    let compare uu___1 =
      FStarC_Format.print_string
        "Comparing times for normalization and nbe\n";
      (let uu___3 =
         let uu___4 = encode (Prims.of_int (1000)) in
         let uu___5 =
           let uu___6 = FStarC_Tests_Util.nm FStarC_Tests_Util.x in
           let uu___7 = FStarC_Tests_Util.nm FStarC_Tests_Util.x in
           minus uu___6 uu___7 in
         let_ FStarC_Tests_Util.x uu___4 uu___5 in
       run_both_with_time (Prims.of_int (14)) uu___3 z) in
    let compare_times l_int =
      fun l_nbe ->
        FStarC_Format.print_string
          "Comparing times for normalization and nbe\n";
        FStarC_List.iter2
          (fun res1 ->
             fun res2 ->
               let uu___2 = res1 in
               match uu___2 with
               | (t1, time_int) ->
                   let uu___3 = res2 in
                   (match uu___3 with
                    | (t2, time_nbe) ->
                        if t1 = t2
                        then
                          let uu___4 =
                            FStarC_Class_Show.show
                              FStarC_Class_Show.showable_int t1 in
                          FStarC_Format.print3
                            "Test %s\nNBE %s\nInterpreter %s\n" uu___4
                            (FStarC_Util.string_of_float time_nbe)
                            (FStarC_Util.string_of_float time_int)
                        else
                          FStarC_Format.print_string
                            "Test numbers do not match...\n")) l_int l_nbe in
    let run_all1 uu___1 =
      (let uu___3 =
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_term znat in
       FStarC_Format.print1 "%s" uu___3);
      (let uu___3 = run_all_whnf_with_time () in
       let l_int = run_all_interpreter_with_time () in
       let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe) in
    run_all1 ()
