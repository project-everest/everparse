let resolve fstar_exe =
  match Options.z3_executable () with
  | Some z3 -> z3
  | None ->
    let version = Z3Version.z3_version in
    let args = [| "--locate_z3"; version |] in
    Printf.printf "Running: %s --locate_z3 %s\n%!" fstar_exe version;
    let result = Process.run fstar_exe args in
    List.iter print_endline result.Process.Output.stdout;
    List.iter prerr_endline result.Process.Output.stderr;
    let output =
      List.filter (fun line -> line <> "")
        (List.map String.trim result.Process.Output.stdout)
    in
    match result.Process.Output.exit_status, output with
    | Process.Exit.Exit 0, [z3] -> z3
    | Process.Exit.Exit 0, _ ->
      failwith "F* --locate_z3 did not return a Z3 executable"
    | _ ->
      let opt_z3 =
        Filename.concat
          (Filename.concat (Filename.concat OS.everparse_home "opt") "z3")
          ("z3-" ^ version)
      in
      if Sys.file_exists opt_z3
      then opt_z3
      else
        failwith
          (Printf.sprintf "Unable to locate Z3 %s; specify --z3_executable" version)
