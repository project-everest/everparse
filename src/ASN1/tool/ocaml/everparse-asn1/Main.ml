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
let files = ref []

let speclist = [
  "--odir", Arg.Set_string odir, "DIR output directory (default: .)";
  "--mname", Arg.Set_string mname, "NAME F* module name (default: from the ASN.1 module name)";
  "--root", Arg.Set_string roots, "A,B,... types for which to generate C functions (default: the types not used by other types)";
  "--keep_bytes", Arg.Set_string keep_bytes, "A,B,... types whose parsed values keep their bytes (as with --#KEEP-BYTES A B in the file)";
  "--fstar_only", Arg.Set fstar_only, " only generate the F* modules";
  "--skip_compilation", Arg.Set skip_compilation, " do not compile the generated C code";
  "--lax_size_of", Arg.Set lax_size_of, " accept SIZE (lo..hi) on SEQUENCE OF / SET OF, but only check lo >= 1 (the validators accept more values than the schema)";
]

let fail fmt = Printf.ksprintf (fun s -> prerr_endline ("everparse-asn1: " ^ s); exit 1) fmt

let file_exists_dir d f = Sys.file_exists (Filename.concat d f)

let everparse_home () =
  match Sys.getenv_opt "EVERPARSE_HOME" with
  | Some h -> h
  | None ->
    let rec up d =
      if file_exists_dir d "src/ASN1/pulse" then d
      else
        let d' = Filename.dirname d in
        if d' = d then fail "cannot find EverParse: please set EVERPARSE_HOME"
        else up d'
    in
    let exe = Sys.executable_name in
    let exe = if Filename.is_relative exe then Filename.concat (Sys.getcwd ()) exe else exe in
    up (Filename.dirname exe)

let write_file path contents =
  let oc = open_out_bin path in
  output_string oc contents;
  close_out oc

let run (args: string list) =
  let cmd = String.concat " " (List.map Filename.quote args) in
  prerr_endline ("+ " ^ cmd);
  match Unix.system cmd with
  | Unix.WEXITED 0 -> ()
  | _ -> fail "command failed: %s" cmd

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
  let r =
    try Elab.elaborate ~lax_size_of:!lax_size_of (List.hd ms) (List.tl ms)
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
  let keep =
    let cli = if !keep_bytes = "" then [] else String.split_on_char ',' !keep_bytes in
    List.sort_uniq compare (List.map (fun a ->
        let n = Elab.mangle a in
        if not (Hashtbl.mem r.env.types n) then fail "KEEP-BYTES: unknown type %s" a;
        n) (cli @ List.concat_map (fun (m: Ast.modul) -> m.keep_bytes) ms))
  in
  let src = String.concat ", " (List.map Filename.basename !files) in
  let spec_src, pulse_src =
    try
      Gen.gen_spec_module r ~src ~spec,
      Gen.gen_pulse_module r ~src ~spec ~pulse ~roots ~keep
    with Ast.Error s -> fail "%s: %s" file s
  in
  let rec mkdir_p d =
    if not (Sys.file_exists d) then begin
      mkdir_p (Filename.dirname d);
      Sys.mkdir d 0o755
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
    let fstar = match Sys.getenv_opt "FSTAR_EXE" with
      | Some f -> f
      | None -> Filename.concat home "opt/FStar/out/bin/fstar.exe"
    in
    let z3 = Filename.concat home "opt/z3/z3-5.3.0" in
    let z3_opts = if Sys.file_exists z3 then ["--smt"; z3; "--z3version"; "5.3.0"] else ["--z3version"; "4.13.3"] in
    let fstar_args = [fstar] @ z3_opts @ [
        "--ext"; "optimize_let_vc"; "--ext"; "context_pruning";
        "--include"; Filename.concat home "lib/everparse/lowparse";
        "--include"; Filename.concat home "src/ASN1";
        "--include"; Filename.concat home "src/ASN1/pulse";
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
