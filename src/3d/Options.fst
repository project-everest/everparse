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

let options =
  let open FStar.Getopt in
  [(noshort, "module_name", OneArg ((fun mname -> module_name := Some mname), "module name"), "module name to use for the output file");
   (noshort, "odir", OneArg ((fun dir -> output_dir := Some dir), "output directory"), "output directory (default 'out'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory");
   (noshort, "error_log", OneArg ((fun l -> error_log := Some l), "error log"), "The stream to which to log errors (default 'stderr')");
   (noshort, "error_log_function", OneArg ((fun l -> error_log_function := Some l), "error logging function"), "The function to use to log errors  (default 'fprintf')");
   (noshort, "debug", ZeroArgs (fun _ -> debug := true), "Emit a lot of debugging output");
   ]

let display_usage () : ML unit =
  FStar.IO.print_string "3d [options] input_file\n";
  List.iter (fun (_, m, _, desc) ->
    FStar.IO.print_string (Printf.sprintf "    --%s %s\n" m desc))
    options

let parse_cmd_line () : ML (list string) =
  let open FStar.Getopt in
  let res = FStar.Getopt.parse_cmdline options (fun file -> input_file := file :: !input_file) in
  match res with
  | Success -> !input_file
  | Help -> display_usage(); exit 0
  | Error s -> FStar.IO.print_string s; exit 1
  | _ -> exit 2

let split_3d_file_name fn =
  match String.split ['.'] fn with
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

let get_module_name () =
  match !module_name with
  | None ->
    begin
    match !input_file with
    | file::_ ->
      begin
      match split_3d_file_name file with
      | Some nm -> nm
      | None -> "DEFAULT"
      end
    | _ -> "DEFAULT"
    end
  | Some s -> s

let get_output_dir () =
  match !output_dir with
  | None -> "out"
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
