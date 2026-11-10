(* everparse-asn1: generate verified DER validators, parsers and writers in C
   from an ASN.1 module *)

let usage = "everparse-asn1 [options] main.asn [imported.asn ...]"

let odir = ref "."
let mname = ref ""
let roots = ref ""
let keep_bytes = ref ""
let fstar_only = ref false
let skip_compilation = ref false
let lax_size_of = ref false
let max_int_union = ref 256
let fstar_exe = ref None
let z3_exe = ref None
let files = ref []

let speclist = [
  "--odir", Arg.Set_string odir, "DIR output directory (default: .)";
  "--mname", Arg.Set_string mname, "NAME F* module name (default: from the ASN.1 module name)";
  "--root", Arg.Set_string roots, "A,B,... types for which to generate C functions (default: the types not used by other types)";
  "--keep_bytes", Arg.Set_string keep_bytes, "A,B.c,... types (or components c of SEQUENCE/SET types B) whose parsed values keep their bytes (as with --#KEEP-BYTES A B.c in the file)";
  "--fstar_only", Arg.Set fstar_only, " only generate the F* modules";
  "--skip_compilation", Arg.Set skip_compilation, " do not compile the generated C code";
  "--max_int_union", Arg.Set_int max_int_union, "N the maximal number of values of a union of INTEGER ranges that is not a single range (default 256; each value is compared in turn by the validators)";
  "--lax_size_of", Arg.Set lax_size_of, " accept SIZE (lo..hi) on SEQUENCE OF / SET OF, but only check lo >= 1 (the validators accept more values than the schema)";
  "--fstar", Arg.String (fun s -> fstar_exe := Some s), "PATH the F* executable (default: $FSTAR_EXE, then the one of EverParse, then fstar.exe in the PATH)";
  "--z3", Arg.String (fun s -> z3_exe := Some s), "PATH the Z3 executable (default: the one found by F*, then the one of EverParse)";
]

let fail fmt = Printf.ksprintf (fun s -> prerr_endline ("everparse-asn1: " ^ s); exit 1) fmt

let filename_is_relative n =
  Filename.is_relative n &&
  not (Sys.win32 && String.length n >= 3 && n.[1] = ':' && (n.[2] = '/' || n.[2] = '\\'))

let get_absolute_filename n =
  if filename_is_relative n then Filename.concat (Sys.getcwd ()) n else n

(* EVERPARSE_HOME if set, else the parent of the directory of this
   executable, which is in bin/, both in the source tree and in the binary
   package *)
let everparse_home () =
  match Sys.getenv_opt "EVERPARSE_HOME" with
  | Some h -> h
  | None ->
    get_absolute_filename (Filename.concat (Filename.dirname Sys.executable_name) Filename.parent_dir_name)

let path home l = List.fold_left Filename.concat home l

let write_file path contents =
  let oc = open_out_bin path in
  output_string oc contents;
  close_out oc

let run_cmd ?(silent = false) prog args =
  let cmd =
    if silent then Filename.quote_command prog ~stdout:Filename.null ~stderr:Filename.null args
    else Filename.quote_command prog args
  in
  if not silent then prerr_endline ("+ " ^ cmd);
  Sys.command cmd

let run = function
  | [] -> assert false
  | prog :: args ->
    if run_cmd prog args <> 0 then fail "command failed: %s" (Filename.quote_command prog args)

let resolve_fstar_exe home =
  match !fstar_exe with
  | Some f -> f
  | None ->
    match Sys.getenv_opt "FSTAR_EXE" with
    | Some f -> f
    | None ->
      let opt_fstar = path home ["opt"; "FStar"; "bin"; "fstar.exe"] in
      if Sys.file_exists opt_fstar then opt_fstar
      else
        (* assume a binary package *)
        let bin_fstar = path home ["bin"; "fstar.exe"] in
        if Sys.file_exists bin_fstar then bin_fstar
        else "fstar.exe" (* rely on PATH *)

let z3_options home fstar =
  let v = Z3Version.z3_version in
  match !z3_exe with
  | Some z3 -> ["--smt"; z3; "--z3version"; v]
  | None ->
    if run_cmd ~silent:true fstar ["--locate_z3"; v] = 0 then ["--z3version"; v]
    else
      let opt_z3 = path home ["opt"; "z3"; "z3-" ^ v] in
      if Sys.file_exists opt_z3 then ["--smt"; opt_z3; "--z3version"; v]
      else ["--z3version"; v]

(* An F* module name component: capitalized, alphanumeric or _ *)
let module_name s =
  let s = String.map (fun c -> match c with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> c | _ -> '_') s in
  String.capitalize_ascii s

let () =
  Arg.parse speclist (fun f -> files := !files @ [f]) usage;
  if !files = [] then (Arg.usage speclist usage; exit 1);
  let file = List.hd !files in
  let ms = List.map (fun f ->
      try Parse.parse_file f
      with Ast.Error s -> fail "%s: %s" f s) !files
  in
  let keep = if !keep_bytes = "" then [] else String.split_on_char ',' !keep_bytes in
  let r =
    if !max_int_union < 1 then (prerr_endline "--max_int_union: expected a positive number"; exit 2);
    if !max_int_union > 256 then
      Printf.eprintf "Warning: --max_int_union %d: large unions make large and slow validators\n%!" !max_int_union;
    try Elab.elaborate ~lax_size_of:!lax_size_of ~max_int_union:!max_int_union ~keep (List.hd ms) (List.tl ms)
    with Ast.Error s -> fail "%s: %s" (String.concat ", " !files) s
  in
  let spec = if !mname <> "" then module_name !mname else module_name r.env.mname in
  let pulse = spec ^ ".Impl" in
  let roots =
    if !roots = "" then r.roots
    else List.map (fun a ->
        let n = Elab.mangle a in
        if not (Hashtbl.mem r.env.types n) then fail "--root: unknown type %s" a;
        n) (String.split_on_char ',' !roots)
  in
  if roots = [] then fail "no root types";
  let src = String.concat ", " (List.map Filename.basename !files) in
  let spec_src, pulse_src =
    try
      Gen.gen_spec_module r ~src ~spec,
      Gen.gen_pulse_module r ~src ~spec ~pulse ~roots
    with Ast.Error s -> fail "%s: %s" file s
  in
  let rec mkdir_p d =
    if not (Sys.file_exists d) then begin
      mkdir_p (Filename.dirname d);
      (try Sys.mkdir d 0o755 with Sys_error _ when Sys.file_exists d -> ())
    end
  in
  mkdir_p !odir;
  let spec_file = Filename.concat !odir (spec ^ ".fst") in
  let pulse_file = Filename.concat !odir (pulse ^ ".fst") in
  write_file spec_file spec_src;
  write_file pulse_file pulse_src;
  prerr_endline ("Wrote " ^ spec_file ^ " and " ^ pulse_file);
  if not !fstar_only then begin
    let home = everparse_home () in
    let fstar = resolve_fstar_exe home in
    let z3_opts = z3_options home fstar in
    let asn1_lib = path home ["lib"; "everparse"; "asn1"] in
    let fstar_args = [fstar] @ z3_opts @ [
        "--ext"; "context_pruning";
        "--include"; path home ["lib"; "everparse"; "lowparse"];
        "--include"; Filename.concat asn1_lib "spec";
        "--include"; Filename.concat asn1_lib "pulse";
        "--include"; !odir;
        "--cache_checked_modules";
        "--already_cached"; Printf.sprintf "*,-%s,-%s" spec pulse;
        "--warn_error"; "@241";
      ] in
    run (fstar_args @ [spec_file]);
    run (fstar_args @ [pulse_file]);
    let c_file = Filename.concat !odir (spec ^ ".c") in
    (* Error 368 (a type with no C representation) would silently produce
       unusable code: make it fatal *)
    run (fstar_args @ ["--warn_error"; "@368"; "--codegen"; "C"; "--custard_monomorphize_types"; "true";
                       "--custard_entry_module"; pulse; pulse_file; "-o"; c_file]);
    prerr_endline ("Wrote " ^ c_file ^ " and " ^ Filename.remove_extension c_file ^ ".h");
    if not !skip_compilation then begin
      let cc = match Sys.getenv_opt "CC" with Some c -> c | None -> "cc" in
      run [cc; "-std=c11"; "-Wall"; "-Wextra"; "-Wno-type-limits"; "-Wno-unused-variable"; "-O1"; "-c";
           "-I"; !odir; c_file; "-o"; Filename.remove_extension c_file ^ ".o"]
    end
  end
