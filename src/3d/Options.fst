module Options
open FStar.All
open FStar.ST
#push-options "--warn_error -272" //top-level effects are okay

let module_name : ref (option string) = alloc None
let output_dir : ref (option string) = alloc None
let input_file : ref (list string) = alloc []
let error_log : ref (option string) = alloc None
let error_log_function : ref (option string) = alloc None
let debug : ref bool = alloc false
let batch : ref bool = alloc false
let clang_format : ref bool = alloc false
let clang_format_executable : ref string = alloc ""

(* We would like to parse --help as an option, but this would
   require to recurse on the definition of the list of options. To
   avoid that, we define this list as mutable, and then we add --help
   after the fact. *)

let options0 =
  let open FStar.Getopt in
  [(noshort, "module_name", OneArg ((fun mname -> module_name := Some mname), "module name"), "module name to use for the output file");
   (noshort, "odir", OneArg ((fun dir -> output_dir := Some dir), "output directory"), "output directory (default '.'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory");
   (noshort, "error_log", OneArg ((fun l -> error_log := Some l), "error log"), "The stream to which to log errors (default 'stderr')");
   (noshort, "error_log_function", OneArg ((fun l -> error_log_function := Some l), "error logging function"), "The function to use to log errors  (default 'fprintf')");
   (noshort, "debug", ZeroArgs (fun _ -> debug := true), "Emit a lot of debugging output");
   (noshort, "batch", ZeroArgs (fun _ -> batch := true), "Verify the generated F* code and extract C code");
   (noshort, "clang_format", ZeroArgs (fun _ -> clang_format := true), "Call clang-format on extracted .c/.h files (--batch only)");
   (noshort, "no_clang_format", ZeroArgs (fun _ -> clang_format := false), "Do not call clang-format on extracted .c/.h files");
   (noshort, "clang_format_executable", OneArg ((fun cmd -> clang_format_executable := cmd), "clang-format full path"), "Provide path to clang-format if not reachable through PATH");
   (noshort, "version", ZeroArgs (fun _ -> FStar.IO.print_string (Printf.sprintf "EverParse/3d %s\nCopyright 2018, 2019, 2020 Microsoft Corporation\n" Version.everparse_version); exit 0), "Show this version of EverParse");
   ]

let options : ref _ = alloc options0

let display_usage () : ML unit =
  FStar.IO.print_string "3d [options] input_file\n";
  List.iter (fun (_, m, _, desc) ->
    FStar.IO.print_string (Printf.sprintf "    --%s %s\n" m desc))
    !options

let _ =
  options := ('h', "help", FStar.Getopt.ZeroArgs (fun _ -> display_usage (); exit 0), "Show this help message") :: !options

let parse_cmd_line () : ML (list string) =
  let open FStar.Getopt in
  let res = FStar.Getopt.parse_cmdline !options (fun file -> input_file := file :: !input_file) in
  match res with
  | Success -> !input_file
  | Help -> display_usage(); exit 0
  | Error s -> FStar.IO.print_string s; exit 1
  | _ -> exit 2

let rec list_last #a (l: list a { Cons? l }) : Tot a =
  match l with
  | [x] -> x
  | _ :: l' -> list_last l'

let basename (fn: string) : Tot string =
  let fn2 =
    match String.split ['\\'] fn with
    | [] -> fn
    | l -> list_last l
  in
  match String.split ['/'] fn2 with
  | [] -> fn2
  | l2 -> list_last l2

let split_3d_file_name fn =
  match String.split ['.'] (basename fn) with
  | [name;extension] ->
    // FStar.IO.print_string
    //   (Printf.sprintf "filename = %s; name=%s; extension=%s"
    //                   fn
    //                   name
    //                   extension);
    if extension = "3d"
    then Some name
    else None
  | _ -> None

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
