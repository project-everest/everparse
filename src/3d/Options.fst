module Options
open HashingOptions
open FStar.All
open FStar.ST
module U8 = FStar.UInt8
module OS = OS

#push-options "--warn_error -272" //top-level effects are okay

let arg0 : ref string = alloc "3d"
let batch : ref bool = alloc false
let check_hashes : ref (option check_hashes_t) = alloc None
let clang_format : ref bool = alloc false
let clang_format_executable : ref string = alloc ""
let cleanup : ref bool = alloc false
let debug : ref bool = alloc false
let error_log : ref (option string) = alloc None
let error_log_function : ref (option string) = alloc None
let inplace_hashes : ref (list string) = alloc []
let input_file : ref (list string) = alloc []
let module_name : ref (option string) = alloc None
let no_everparse_h : ref bool = alloc false
let output_dir : ref (option string) = alloc None
let save_hashes : ref bool = alloc false
let skip_makefiles : ref bool = alloc false

let set_check_hashes = function
| "none" -> check_hashes := None
| "weak" -> batch := true; check_hashes := Some WeakHashes
| "strong" -> batch := true; check_hashes := Some StrongHashes
| "inplace" -> batch := true; check_hashes := Some InplaceHashes
| _ -> ()

(* We would like to parse --help as an option, but this would
   require to recurse on the definition of the list of options. To
   avoid that, we define this list as mutable, and then we add --help
   after the fact. *)

let options0 =
  let open FStar.Getopt in
  [
   (noshort, "batch", ZeroArgs (fun _ -> batch := true), "Verify the generated F* code and extract C code");
   (noshort, "check_hashes", OneArg (set_check_hashes, "none|weak|strong"), "Check hashes");
   (noshort, "check_inplace_hash", OneArg ((fun c -> inplace_hashes := c :: !inplace_hashes), "file.3d=file.h"), "Check hashes stored in one .h/.c file");
   (noshort, "clang_format", ZeroArgs (fun _ -> batch := true; clang_format := true), "Call clang-format on extracted .c/.h files (--batch only)");
   (noshort, "clang_format_executable", OneArg ((fun cmd -> batch := true; clang_format := true; clang_format_executable := cmd), "clang-format full path"), "Provide path to clang-format if not reachable through PATH");
   (noshort, "cleanup", ZeroArgs (fun _ -> cleanup := true), "Remove *.fst*, *.krml and kremlin-args.rsp (--batch only)");
   (noshort, "copy_everparse_h", ZeroArgs (fun _ -> no_everparse_h := false), "Copy EverParse.h (--batch only)");
   (noshort, "debug", ZeroArgs (fun _ -> debug := true), "Emit a lot of debugging output");
   (noshort, "error_log", OneArg ((fun l -> error_log := Some l), "error log"), "The stream to which to log errors (default 'stderr')");
   (noshort, "error_log_function", OneArg ((fun l -> error_log_function := Some l), "error logging function"), "The function to use to log errors  (default 'fprintf')");
   (noshort, "no_batch", ZeroArgs (fun _ -> batch := false), "Do not verify the generated F* code or extract C code");
   (noshort, "no_clang_format", ZeroArgs (fun _ -> clang_format := false), "Do not call clang-format on extracted .c/.h files");
   (noshort, "no_cleanup", ZeroArgs (fun _ -> cleanup := false), "Do not remove *.fst*, *.krml or kremlin-args.rsp");
   (noshort, "no_copy_everparse_h", ZeroArgs (fun _ -> no_everparse_h := true), "Do not copy EverParse.h");
   (noshort, "no_save_hashes", ZeroArgs (fun _ -> save_hashes := false), "Do not save hashes");
   (noshort, "no_skip_makefiles", ZeroArgs (fun _ -> skip_makefiles := false), "Generate Makefile.basic, Makefile.include (--batch only)");
   (noshort, "odir", OneArg ((fun dir -> output_dir := Some dir), "output directory"), "output directory (default '.'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory");
   (noshort, "save_hashes", ZeroArgs (fun _ -> save_hashes := true), "Save hashes");
   (noshort, "skip_makefiles", ZeroArgs (fun _ -> skip_makefiles := true), "Do not generate Makefile.basic, Makefile.include");
   (noshort, "version", ZeroArgs (fun _ -> FStar.IO.print_string (Printf.sprintf "EverParse/3d %s\nCopyright 2018, 2019, 2020 Microsoft Corporation\n" Version.everparse_version); exit 0), "Show this version of EverParse");
   (noshort, "module_name", OneArg ((fun mname -> module_name := Some mname), "module name"), "module name to use for the output file");
   ]

let options : ref _ = alloc options0

let display_usage () : ML unit =
  FStar.IO.print_string "EverParse/3d: verified data validation with dependent data descriptions\n";
  FStar.IO.print_string "\n";
  FStar.IO.print_string (Printf.sprintf "Usage: %s [options] path_to_input_file1.3d path_to_input_file2.3d ... \n" !arg0);
  FStar.IO.print_string "\n";
  FStar.IO.print_string "Options:\n";
  List.iter (fun (_, m, arg, desc) ->
    let argdesc = match arg with
    | FStar.Getopt.OneArg (_, argdesc) -> Printf.sprintf " <%s>" argdesc
    | _ -> ""
    in
    FStar.IO.print_string (Printf.sprintf "--%s%s\n\t%s\n" m argdesc desc))
    !options
      ;
  FStar.IO.print_string "\n";
  if !batch then begin
    FStar.IO.print_string "--batch is currently toggled.\n";
    if !clang_format then begin
      FStar.IO.print_string "--clang_format is currently toggled.\n"
    end;
    if !cleanup then begin
      FStar.IO.print_string "--cleanup is currently toggled.\n"
    end;
    if !skip_makefiles then begin
      FStar.IO.print_string "--skip_makefiles is currently toggled.\n"
    end;
    if not !no_everparse_h then begin
      FStar.IO.print_string "--copy_everparse_h is currently toggled.\n"
    end;
    let chk = match !check_hashes with
    | None -> "none"
    | Some WeakHashes -> "weak"
    | Some StrongHashes -> "strong"
    | Some InplaceHashes -> "inplace"
    in
    FStar.IO.print_string (Printf.sprintf "--check_hashes is currently set to %s.\n" chk);
    if !save_hashes then begin
      FStar.IO.print_string "--save_hashes is currently toggled.\n"
    end;
    ()
  end

let _ =
  options := ('h', "help", FStar.Getopt.ZeroArgs (fun _ -> display_usage (); exit 0), "Show this help message") :: !options

let hidden_options =
  let open FStar.Getopt in
  [
    (noshort, "__arg0", OneArg ((fun s -> arg0 := s), "executable name"), "executable name to use for the help message");
  ]

let parse_cmd_line () : ML (list string) =
  let open FStar.Getopt in
  let res = FStar.Getopt.parse_cmdline (hidden_options `List.Tot.append` !options) (fun file -> input_file := file :: !input_file) in
  match res with
  | Success -> !input_file
  | Help -> display_usage(); exit 0
  | Error s -> FStar.IO.print_string s; exit 1
  | _ -> exit 2

let split_3d_file_name fn =
  let fn = OS.basename fn in
  if OS.extension fn = ".3d"
  then Some (OS.remove_extension fn)
  else None

let get_file_name mname = mname ^ ".3d"

let get_module_name (file: string) =
  match !module_name with
  | None ->
    begin
    match split_3d_file_name file with
    | Some nm -> nm
    | None -> "DEFAULT"
    end
  | Some s ->
    match !input_file with
    | _ :: _ :: _ ->
      failwith "module_name not allowed if several files are provided"
    | _ -> s

let get_output_dir () =
  match !output_dir with
  | None -> "."
  | Some s -> s

let get_error_log () =
  match !error_log with
  | None -> "stderr"
  | Some s -> s

let get_error_log_function () =
  match !error_log_function with
  | None -> "fprintf"
  | Some s -> s

let debug_print_string (s:string): ML unit =
  if !debug
  then FStar.IO.print_string s
  else ()

let get_batch () =
  !batch

let get_clang_format () =
  !clang_format

let get_clang_format_executable () =
  !clang_format_executable

let get_cleanup () =
  !cleanup

let get_skip_makefiles () =
  !skip_makefiles

let get_no_everparse_h () =
  !no_everparse_h

let get_check_hashes () =
  if !batch then !check_hashes else None

let get_save_hashes () =
  !save_hashes

let get_check_inplace_hashes () =
  List.rev !inplace_hashes
