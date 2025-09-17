open Fstarcompiler
open Prims
let (handle_error : Prims.exn -> unit) =
  fun e ->
    (let uu___1 = FStarC_Errors.handleable e in
     if uu___1
     then FStarC_Errors.err_exn e
     else
       ((let uu___4 = FStarC_Util.message_of_exn e in
         FStarC_Format.print1_error "Unexpected error: %s\n" uu___4);
        (let uu___4 = FStarC_Options.trace_error () in
         if uu___4
         then
           let uu___5 = FStarC_Util.trace_of_exn e in
           FStarC_Format.print1_error "Trace:\n%s\n" uu___5
         else
           FStarC_Format.print_error
             "Please file a bug report, ideally with a minimized version of the source program that triggered the error.\n")));
    (let uu___2 = FStarC_Errors.report_all () in ())
let main : 'uuuuu . unit -> 'uuuuu =
  fun uu___ ->
    FStarC_Format.print_string "Initializing tests...\n";
    (try
       (fun uu___2 ->
          match () with
          | () ->
              let uu___3 = FStarC_Options.parse_cmd_line () in
              (match uu___3 with
               | (res, fs) ->
                   (match res with
                    | FStarC_Getopt.Error (msg, uu___4) ->
                        (FStarC_Format.print_error msg;
                         FStarC_Effect.exit Prims.int_one)
                    | FStarC_Getopt.Empty ->
                        ((let uu___5 =
                            FStarC_Options.set_options
                              "--error_contexts true" in
                          ());
                         (let uu___6 = FStarC_Debug.any () in
                          if uu___6
                          then
                            ((let uu___8 =
                                FStarC_Effect.op_Bang FStarC_Options._version in
                              let uu___9 =
                                FStarC_Effect.op_Bang FStarC_Options._commit in
                              let uu___10 = FStarC_Platform_Base.kernel () in
                              FStarC_Format.print3
                                "- F* version %s -- %s (on %s)\n" uu___8
                                uu___9 uu___10);
                             FStarC_Format.print1 "- Executable: %s\n"
                               FStarC_Util.exec_name;
                             (let uu___10 =
                                let uu___11 = FStarC_Find.lib_root () in
                                FStarC_Option.dflt "<none>" uu___11 in
                              FStarC_Format.print1 "- Library root: %s\n"
                                uu___10);
                             (let uu___11 =
                                let uu___12 =
                                  FStarC_Find.full_include_path () in
                                FStarC_Class_Show.show
                                  (FStarC_Class_Show.show_list
                                     FStarC_Class_Show.showable_string)
                                  uu___12 in
                              FStarC_Format.print1
                                "- Full include path: %s\n" uu___11);
                             FStarC_Format.print_string "\n")
                          else ());
                         FStarC_Tests_Pars.do_init ();
                         FStarC_Tests_Pars.parse_incremental_decls ();
                         FStarC_Tests_Pars.parse_incremental_decls_use_lang
                           ();
                         FStarC_Tests_Norm.run_all ();
                         (let uu___11 = FStarC_Tests_Unif.run_all () in
                          if uu___11
                          then ()
                          else FStarC_Effect.exit Prims.int_one);
                         FStarC_Tests_Data.run_all ();
                         (let uu___13 = FStarC_Errors.report_all () in ());
                         (let nerrs = FStarC_Errors.get_err_count () in
                          if nerrs > Prims.int_zero
                          then
                            ((let uu___15 = FStarC_Errors.report_all () in ());
                             FStarC_Effect.exit Prims.int_one)
                          else ();
                          FStarC_Effect.exit Prims.int_zero))
                    | FStarC_Getopt.Success ->
                        ((let uu___5 =
                            FStarC_Options.set_options
                              "--error_contexts true" in
                          ());
                         (let uu___6 = FStarC_Debug.any () in
                          if uu___6
                          then
                            ((let uu___8 =
                                FStarC_Effect.op_Bang FStarC_Options._version in
                              let uu___9 =
                                FStarC_Effect.op_Bang FStarC_Options._commit in
                              let uu___10 = FStarC_Platform_Base.kernel () in
                              FStarC_Format.print3
                                "- F* version %s -- %s (on %s)\n" uu___8
                                uu___9 uu___10);
                             FStarC_Format.print1 "- Executable: %s\n"
                               FStarC_Util.exec_name;
                             (let uu___10 =
                                let uu___11 = FStarC_Find.lib_root () in
                                FStarC_Option.dflt "<none>" uu___11 in
                              FStarC_Format.print1 "- Library root: %s\n"
                                uu___10);
                             (let uu___11 =
                                let uu___12 =
                                  FStarC_Find.full_include_path () in
                                FStarC_Class_Show.show
                                  (FStarC_Class_Show.show_list
                                     FStarC_Class_Show.showable_string)
                                  uu___12 in
                              FStarC_Format.print1
                                "- Full include path: %s\n" uu___11);
                             FStarC_Format.print_string "\n")
                          else ());
                         FStarC_Tests_Pars.do_init ();
                         FStarC_Tests_Pars.parse_incremental_decls ();
                         FStarC_Tests_Pars.parse_incremental_decls_use_lang
                           ();
                         FStarC_Tests_Norm.run_all ();
                         (let uu___11 = FStarC_Tests_Unif.run_all () in
                          if uu___11
                          then ()
                          else FStarC_Effect.exit Prims.int_one);
                         FStarC_Tests_Data.run_all ();
                         (let uu___13 = FStarC_Errors.report_all () in ());
                         (let nerrs = FStarC_Errors.get_err_count () in
                          if nerrs > Prims.int_zero
                          then
                            ((let uu___15 = FStarC_Errors.report_all () in ());
                             FStarC_Effect.exit Prims.int_one)
                          else ();
                          FStarC_Effect.exit Prims.int_zero))))) ()
     with | uu___2 -> (handle_error uu___2; FStarC_Effect.exit Prims.int_one))
