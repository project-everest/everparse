module GenMakefile
module OS = OS

type rule_type =
  | EverParse
  | EverParseGroup of list string
  | CC
  | Nop (* to simulate multiple-target rules *)

type rule_t = {
  ty: rule_type;
  from: list string;
  to: string;
  args: string;
}

let input_dir = "$(EVERPARSE_INPUT_DIR)"
let output_dir = "$(EVERPARSE_OUTPUT_DIR)"

let oext = function
| HashingOptions.MakefileGMake -> "o"
| HashingOptions.MakefileNMake -> "obj"

let mk_rule_operand (mtype: HashingOptions.makefile_type) (op: string) : Tot string =
  match mtype with
  | HashingOptions.MakefileGMake -> OS.replace_backslashes op // GNU Make uses `/` even on Windows
  | _ -> op

let print_make_rule
  mtype
  everparse_h
  input_stream_binding
  (api: HashingOptions.api_t)
  (makefile: string)
  (r: rule_t)
: Tot string
=
  let pulse = api = HashingOptions.ApiPulse in
  let deps = match r.ty with
    | EverParse | EverParseGroup _ -> r.from @ [makefile]
    | _ -> r.from
  in
  let outputs = r.to :: (match r.ty with EverParseGroup others -> others | _ -> []) in
  let separator = match mtype, r.ty with
    | HashingOptions.MakefileGMake, EverParseGroup _ -> "&:"
    | _ -> ":"
  in
  let rule = Printf.sprintf "%s %s %s\n"
    (String.concat " " (List.Tot.map (mk_rule_operand mtype) outputs))
    separator (String.concat " " (List.Tot.map (mk_rule_operand mtype) deps)) in
  match r.ty with
  | Nop -> Printf.sprintf "%s\n" rule
  | _ ->
    let cmd =
      match r.ty with
      | EverParse | EverParseGroup _ -> Printf.sprintf "$(EVERPARSE_CMD) --api %s --odir %s" (HashingOptions.string_of_api api) output_dir
      | CC ->
        let iopt = match mtype with
          | HashingOptions.MakefileGMake -> "-I"
          | HashingOptions.MakefileNMake -> "/I"
        in
        let inc =
          if everparse_h
          then ""
          else
            let lib_3d_home = "$(EVERPARSE_HOME)" `OS.concat` "lib" `OS.concat` "everparse" `OS.concat` "3d" in
            (* With --no_copy_everparse_h the client compiles against a prebuilt
               EverParse.h rather than a copy in the output directory, so the
               include path has to name the runtime matching the API and
               backend: krml/<backend> for --api pulse, krml/lowstar/<backend>
               for --api lowstar. lib_3d_home still supplies
               EverParsePulse{,Endianness}.h and EverParseEndianness.h. *)
            let ddd_actions_home =
              let krml = lib_3d_home `OS.concat` "krml" in
              let runtime = if pulse then krml else krml `OS.concat` "lowstar" in
              runtime `OS.concat` (HashingOptions.string_of_input_stream_binding input_stream_binding)
            in
            Printf.sprintf "%s %s %s %s" iopt lib_3d_home iopt ddd_actions_home
        in
        let copt = match mtype with
        | HashingOptions.MakefileGMake -> "-c"
        | HashingOptions.MakefileNMake -> "/c"
        in
        Printf.sprintf "$(CC) $(CFLAGS) %s %s %s %s %s %s" iopt input_dir iopt output_dir inc copt
    in
    let rule = Printf.sprintf "%s\t%s %s\n\n" rule cmd r.args in
    rule

let mk_input_filename
  (file: string)
: Tot string
= input_dir `OS.concat` OS.basename file

let mk_filename
  (modul: string)
  (ext: string)
: Tot string
= output_dir `OS.concat` (Printf.sprintf "%s.%s" modul ext)

let add_cfg_file_dep ext deps
  : FStar.All.ML (list string)
  = match Options.config_module_name () with
    | None -> deps
    | Some module_name -> deps `List.Tot.append` [mk_filename module_name ext]
  
let produce_config_fst_file_rule ()
: FStar.All.ML (list rule_t)
= match Options.config_module_name (), Options.get_config_file() with
  | Some module_name, Some cfg_file_name ->
    let fst_file_name = mk_filename module_name "fst" in
    let checked_file_name = mk_filename module_name "fst.checked" in
    let fst_rule = {
      ty = EverParse;
      from = [cfg_file_name];
      to = fst_file_name;
      args = "--__micro_step emit_config"
    } in
    let fst_checked_rule = {
      ty = EverParse;
      from = [fst_file_name];
      to =  checked_file_name;
      args = Printf.sprintf "--__micro_step verify %s" fst_file_name;
    } in
    [fst_rule; fst_checked_rule]
  | _ -> []

let has_external_types_fsti
  (g: Deps.dep_graph)
  (modul: string)
: Tot bool
= 
  (Deps.has_output_types g modul ||
    Deps.has_extern_types g modul)

let maybe_external_types_fsti_checked
  (g: Deps.dep_graph)
  (modul: string)
: Tot (list string)
= if has_external_types_fsti g modul
  then [mk_filename modul "ExternalTypes.fsti.checked"]
  else []

let has_external_api_fsti
  (g: Deps.dep_graph)
  (modul: string)
: Tot bool
=
  Deps.has_extern_probe g modul ||
  Deps.has_out_exprs g modul ||
  Deps.has_extern_types g modul ||
  Deps.has_extern_functions g modul

let produce_external_api_fsti_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: list rule_t
= if not (has_external_api_fsti g modul) then []
  else
    let external_api_fsti = mk_filename modul "ExternalAPI.fsti" in
    [{
      ty = EverParse;
       from = external_api_fsti :: (maybe_external_types_fsti_checked g modul `List.Tot.append` List.Tot.map (fun m -> mk_filename m "fsti.checked") (Deps.dependencies g modul));
       to = mk_filename modul "ExternalAPI.fsti.checked";
       args = Printf.sprintf "--__micro_step verify %s" external_api_fsti;
     }]

let produce_external_types_fsti_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: list rule_t
= if not (has_external_types_fsti g modul) then []
  else
    let external_types_fsti = mk_filename modul "ExternalTypes.fsti" in 
    [{
       ty = EverParse;
       from = external_types_fsti :: List.Tot.map (fun m -> mk_filename m "ExternalTypes.fsti.checked") (Deps.dependencies g modul);
       to = mk_filename modul "ExternalTypes.fsti.checked";
       args = Printf.sprintf "--__micro_step verify %s" external_types_fsti;
     }]

let maybe_external_api_fsti_checked
  (g: Deps.dep_graph)
  (modul: string)
: Tot (list string)
= if has_external_api_fsti g modul
  then [mk_filename modul "ExternalAPI.fsti.checked"]
  else []

let external_deps
  (g: Deps.dep_graph)
  (modul: string)
: Tot (list string)
= maybe_external_types_fsti_checked g modul `List.Tot.append`
  maybe_external_api_fsti_checked g modul

let produce_fsti_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
= let fsti = mk_filename modul "fsti" in
  {
    ty = EverParse;
    from = fsti :: (external_deps g modul `List.Tot.append` List.Tot.map (fun m -> mk_filename m "fsti.checked") (Deps.dependencies g modul));
    to = mk_filename modul "fsti.checked";
    args = Printf.sprintf "--__micro_step verify %s" fsti;
  }

let produce_fst_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: FStar.All.ML rule_t
= let fst = mk_filename modul "fst" in
  {
    ty = EverParse;
    from = add_cfg_file_dep "fst.checked" (fst :: mk_filename modul "fsti.checked" :: List.Tot.map (fun m -> mk_filename m "fsti.checked") (Deps.dependencies g modul));
    to = mk_filename modul "fst.checked";
    args = Printf.sprintf "--__micro_step verify %s" fst;
  }

let maybe_external_typedefs_h
  (emit_output_types_defs: bool)
  (g:Deps.dep_graph)
  (modul: string)
: Tot (list string)
= if (Deps.has_output_types g modul && not (Deps.has_extern_types g modul)) && emit_output_types_defs
  then [mk_filename (Printf.sprintf "%s_ExternalTypedefs" modul) "h"]
  else []

let produce_fst_rules
  (emit_output_types_defs: bool)
  (g: Deps.dep_graph)
  (clang_format: bool)
  (file: string)
: FStar.All.ML (list rule_t)
=
  let modul = Options.module_name file in
  (* follow the order prescribed by Main.process_file *)
  (* fst* files generated by 3d (cf. Main.emit_fstar_code_for_interpreter) *)
  let first_fst :: other_fst =
    begin
      if has_external_types_fsti g modul
      then [mk_filename modul "ExternalTypes.fsti"]
      else []
    end `List.Tot.append`
    begin
      if has_external_api_fsti g modul
      then [mk_filename modul "ExternalAPI.fsti"]
      else []
    end `List.Tot.append`
      [
        mk_filename modul "fst";
        mk_filename modul "fsti";
      ]
  in
  (* C files generated by 3d (as opposed to F*, cf. Main.emit_entrypoint) *)
  let produced_c =
    begin
      if Deps.has_entrypoint g modul
      then
        [
          mk_filename (Printf.sprintf "%sWrapper" modul) "c";
          mk_filename (Printf.sprintf "%sWrapper" modul) "h";
        ]
      else []
    end `List.Tot.append`
    begin
      if emit_output_types_defs
      then
        if Deps.has_output_types g modul
        then
          mk_filename (Printf.sprintf "%s_OutputTypesDefs" modul) "h" ::
          begin
            if not (Deps.has_extern_types g modul)
            then [mk_filename (Printf.sprintf "%s_ExternalTypedefs" modul) "h"]
            else []
          end
        else []
      else []
    end `List.Tot.append`
    begin
      if Deps.has_out_exprs g modul
      then [mk_filename (Printf.sprintf "%s_OutputTypes" modul) "c"]
      else []
    end `List.Tot.append`
    begin
      if Deps.has_static_assertions g modul
      then [mk_filename (Printf.sprintf "%sStaticAssertions" modul) "c"]
      else []
    end
  in
  (* produce the actual rules *)
    {
      ty = EverParseGroup (other_fst `List.Tot.append` produced_c);
      from =
        (if clang_format then [mk_filename "" "clang-format"] else []) `List.Tot.append`
        (if OS.file_exists (Printf.sprintf "%s.copyright.txt" file) then [mk_input_filename (Printf.sprintf "%s.copyright.txt" file)] else []) `List.Tot.append`
        [mk_input_filename file];
      to = first_fst;
      args = Printf.sprintf "--no_batch %s" (mk_input_filename file);
    } :: []

let maybe_external_types_h
  (g: Deps.dep_graph)
  (m: string)
: Tot (list string)
= if has_external_types_fsti g m
  then [mk_filename (Printf.sprintf "%s_ExternalTypes" m) "h"]
  else []

let maybe_external_api_h
  (g: Deps.dep_graph)
  (m: string)
: Tot (list string)
= if has_external_api_fsti g m
  then [mk_filename (Printf.sprintf "%s_ExternalAPI" m) "h"]
  else []

let maybe_native_generated_h
  (g: Deps.dep_graph)
  (m: string)
: Tot (list string)
= maybe_external_types_h g m `List.Tot.append`
  maybe_external_api_h g m

let maybe_h
  (emit_output_types_defs: bool)
  (g: Deps.dep_graph)
  (m: string)
: Tot (list string)
= maybe_native_generated_h g m `List.Tot.append`
  maybe_external_typedefs_h emit_output_types_defs g m

let produce_h_rules
  (g: Deps.dep_graph)
  (clang_format: bool)
  (file: string)
: FStar.All.ML (list rule_t)
=
  let all_files = Deps.collect_and_sort_dependencies_from_graph g [file] in
  let modul = Options.module_name file in
  let to = mk_filename modul "c" in
  let runtime =
    let home = "$(EVERPARSE_HOME)" `OS.concat` "lib" `OS.concat` "everparse" `OS.concat` "3d" `OS.concat` "krml" in
    let home = if Options.uses_pulse_api () then home else home `OS.concat` "lowstar" in
    home `OS.concat` (HashingOptions.string_of_input_stream_binding (Options.get_input_stream_binding ())) `OS.concat` "EverParse.cui"
  in
  let copyright = mk_input_filename (Printf.sprintf "%s.3d.copyright.txt" (Options.module_name file)) in
  {
    ty = EverParseGroup
      ([mk_filename modul "h"; mk_filename modul "cui"] `List.Tot.append` maybe_native_generated_h g modul);
    from =
      add_cfg_file_dep "fst.checked" (
        [runtime; mk_filename modul "fst.checked"] `List.Tot.append`
        external_deps g modul `List.Tot.append`
        (if clang_format then [mk_filename "" "clang-format"] else []) `List.Tot.append`
        (if OS.file_exists (Printf.sprintf "%s.copyright.txt" file) then [copyright] else []) `List.Tot.append`
        List.map (fun f -> mk_filename (Options.module_name f) "cui")
          (List.filter (fun f -> Options.module_name f <> modul) all_files)
      )
      ;
    to = to;
    args = Printf.sprintf "--__produce_c_from_existing_checked %s" (mk_input_filename file);
  } :: []

let c_to_o mtype o c =
  let oflag = match mtype with
  | HashingOptions.MakefileGMake -> "-o"
  | HashingOptions.MakefileNMake -> "/Fo:"
  in
  Printf.sprintf "%s %s %s" oflag o c

let produce_output_types_o_rule
  mtype
  (emit_output_types_defs: bool)
  (g:Deps.dep_graph)
  (modul:string)
: FStar.All.ML (list rule_t)
=
  if Deps.has_out_exprs g modul
  then
    let c = mk_filename (Printf.sprintf "%s_OutputTypes" modul) "c" in
    let o = mk_filename (Printf.sprintf "%s_OutputTypes" modul) (oext mtype) in
    [{
      ty = CC;
      from = c :: maybe_external_typedefs_h emit_output_types_defs g modul;
      to = o;
      args = c_to_o mtype o c; }]
  else
    []

let produce_o_rule
  mtype
  (everparse_h: bool)
  (modul: string)
: Tot rule_t
=
  let c = mk_filename modul "c" in
  let o = mk_filename modul (oext mtype) in
  {
    ty = CC;
    from = ((if everparse_h then [mk_filename "EverParse" "h"] else []) `List.Tot.append` [c; mk_filename modul "h"]);
    to = o;
    args = c_to_o mtype o c;
  }

let produce_wrapper_o_rule
  mtype
  (everparse_h: bool)
  (g: Deps.dep_graph)
  (modul: string)
: Tot (list rule_t)
=
  let wc = mk_filename (Printf.sprintf "%sWrapper" modul) "c" in
  let wh = mk_filename (Printf.sprintf "%sWrapper" modul) "h" in
  let wo = mk_filename (Printf.sprintf "%sWrapper" modul) (oext mtype) in
  let h = mk_filename modul "h" in
  if Deps.has_entrypoint g modul
  then [{
    ty = CC;
    from =((if everparse_h then [mk_filename "EverParse" "h"] else []) `List.Tot.append` [wc; wh; h]);
    to = wo;
    args = c_to_o mtype wo wc;
  }]
  else []

let produce_static_assertions_o_rule
  mtype
  (everparse_h: bool)
  (g: Deps.dep_graph)
  (modul: string)
: Tot (list rule_t)
=
  let wc = mk_filename (Printf.sprintf "%sStaticAssertions" modul) "c" in
  let wo = mk_filename (Printf.sprintf "%sStaticAssertions" modul) (oext mtype) in
  let h = mk_filename modul "h" in
  if Deps.has_static_assertions g modul
  then [{
    ty = CC;
    from = ((if everparse_h then [mk_filename "EverParse" "h"] else []) `List.Tot.append` [wc; h]);
    to = wo;
    args = c_to_o mtype wo wc;
  }]
  else []

let produce_clang_format_rule
  (clang_format: bool)
  (copy_clang_format_opt: bool)
: Tot (list rule_t)
=
  if clang_format && copy_clang_format_opt
  then [{
   ty = EverParse;
   from = [];
   to = mk_filename "" "clang-format";
   args = "--__micro_step copy_clang_format";
  }] else []

let static_prelude_headers () : FStar.All.ML (list string) =
  match Options.get_input_stream_binding () with
  | HashingOptions.InputStreamStatic _ | HashingOptions.InputStreamExtern _ ->
    [mk_filename "EverParseStreamPrimitives" "h"]
  | _ -> []

let produce_everparse_h_rule
  (everparse_h: bool)
  (all_modules: list string)
: FStar.All.ML (list rule_t)
=
  if everparse_h
  then [
    {
      ty = EverParse;
      from = [];
      to = mk_filename "EverParseEndianness" "h";
      args = "--__micro_step copy_everparse_h EverParseEndianness.h";
    };
  ] `List.Tot.append`
  (* In --api pulse mode the copy_everparse_h micro-step also copies
     EverParsePulseEndianness.h (included by EverParse.h) and EverParsePulse.h
     (included by every <Mod>Wrapper.c). They need their own rules, otherwise
     make cannot repair them.

     Each rule names the headers its own run is responsible for, so that no two
     rules ever write the same file. These rules used to be chained instead,
     with every run re-copying every header. That kept two runs from overlapping
     but did nothing about their *consumers*: once the first link finished, make
     was free to compile against EverParseEndianness.h while the second link was
     rewriting it, which is exactly what it did. *)
  begin if Options.uses_pulse_api ()
  then [
    {
      ty = EverParse;
      from = [];
      to = mk_filename "EverParsePulseEndianness" "h";
      args = "--__micro_step copy_everparse_h EverParsePulseEndianness.h";
    };
    {
      ty = EverParse;
      from = [];
      to = mk_filename "EverParsePulse" "h";
      args = "--__micro_step copy_everparse_h EverParsePulse.h";
    };
  ] else []
  end `List.Tot.append`
  (let headers = static_prelude_headers () in
   List.Tot.map (fun header -> {
     ty = EverParse;
     from = [];
     to = header;
     args = "--__micro_step copy_everparse_h EverParseStreamPrimitives.h";
   }) headers) `List.Tot.append`
  [
    {
      ty = EverParse;
      (* Only this rule writes the shared runtime header. Waiting for native
         units also preserves the build entrypoint based on ALL_H_FILES. *)
      from =
        (static_prelude_headers ()) `List.Tot.append`
        (if Options.uses_pulse_api ()
        then mk_filename "EverParsePulse" "h" ::
             mk_filename "EverParsePulseEndianness" "h" ::
             mk_filename "EverParseEndianness" "h" ::
             List.Tot.map (fun m -> mk_filename m "c") all_modules
        else [mk_filename "EverParseEndianness" "h"]);
      to = mk_filename "EverParse" "h";
      args = "--__micro_step copy_everparse_h EverParse.h";
    }
  ] else []

let produce_hash_rule
  (g: Deps.dep_graph)
  (file: string)
: FStar.All.ML rule_t
=
  let modul = Options.module_name file in
  let deps =
    [mk_input_filename file;
     mk_filename modul "c";
     mk_filename modul "h"]
    `List.Tot.append`
    (if Deps.has_entrypoint g modul
     then [mk_filename (Printf.sprintf "%sWrapper" modul) "c";
           mk_filename (Printf.sprintf "%sWrapper" modul) "h"]
     else [])
    `List.Tot.append`
    (if Deps.has_static_assertions g modul
     then [mk_filename (Printf.sprintf "%sStaticAssertions" modul) "c"]
     else [])
  in
  {
    ty = EverParse;
    from = deps;
    to = mk_filename modul "json";
    args = Printf.sprintf "--__micro_step save_hashes %s" (mk_input_filename file);
  }

noeq
type produce_makefile_res = {
  rules: list rule_t;
  graph: Deps.dep_graph;
  all_files: list string;
}

let produce_makefile
  mtype
  (everparse_h: bool)
  (emit_output_types_defs: bool)
  (skip_o_rules: bool)
  (clang_format: bool)
  (copy_clang_format_opt: bool)
  (save_hashes: bool)
  (files: list string)
: FStar.All.ML produce_makefile_res
=
  let g = Deps.build_dep_graph_from_list files in
  let all_files = Deps.collect_and_sort_dependencies_from_graph g files in
  let all_modules = List.map Options.module_name all_files in
  let rules =
    produce_everparse_h_rule everparse_h all_modules `List.Tot.append`
    produce_clang_format_rule clang_format copy_clang_format_opt `List.Tot.append`
    (if skip_o_rules then [] else
      List.Tot.concatMap (produce_wrapper_o_rule mtype everparse_h g) all_modules `List.Tot.append`
      List.Tot.concatMap (produce_static_assertions_o_rule mtype everparse_h g) all_modules `List.Tot.append`
      List.concatMap (produce_output_types_o_rule mtype emit_output_types_defs g) all_modules `List.Tot.append`
      List.Tot.map (produce_o_rule mtype everparse_h) all_modules
    ) `List.Tot.append`
    List.concatMap (produce_fst_rules emit_output_types_defs g clang_format) all_files `List.Tot.append`
    List.concatMap (produce_external_types_fsti_checked_rule g) all_modules `List.Tot.append`
    List.concatMap (produce_external_api_fsti_checked_rule g) all_modules `List.Tot.append`
    List.Tot.map (produce_fsti_checked_rule g) all_modules `List.Tot.append`
    List.map (produce_fst_checked_rule g) all_modules `List.Tot.append`
    List.concatMap (produce_h_rules g clang_format) all_files `List.Tot.append`
    produce_config_fst_file_rule () `List.Tot.append`
    (if save_hashes then List.map (produce_hash_rule g) all_files else [])
  in {
    graph = g;
    rules = rules;
    all_files = all_files;
  }

let write_makefile
  mtype
  input_stream_binding
  (everparse_h: bool)
  (emit_output_types_defs: bool)
  (skip_o_rules: bool)
  (clang_format: bool)
  (copy_clang_format_opt: bool)
  (save_hashes: bool)
  (files: list string)
: FStar.All.ML unit
=
  let makefile_final = Options.get_makefile_name () in
  let makefile_tmp = makefile_final ^ ".tmp" in
  let file = FStar.IO.open_write_file makefile_tmp in
  (match mtype with
   | HashingOptions.MakefileGMake ->
     FStar.IO.write_string file
       "ifeq (,$(filter grouped-target,$(.FEATURES)))\n$(error EverParse requires GNU Make 4.3 or newer)\nendif\n\n"
   | _ -> ());
  let {graph = g; rules; all_files} = produce_makefile mtype everparse_h emit_output_types_defs skip_o_rules clang_format copy_clang_format_opt save_hashes files in
  FStar.IO.write_string file (String.concat "" (List.Tot.map (print_make_rule mtype everparse_h input_stream_binding (Options.get_api ()) makefile_final) rules));
  let write_all_ext_files (ext_cap: string) (ext: string) : FStar.All.ML unit =
    let ln =
      begin if ext = "h" && everparse_h
      then [mk_filename "EverParse" "h"; mk_filename "EverParseEndianness" "h"] `List.Tot.append`
           static_prelude_headers () `List.Tot.append`
           (* --api pulse additionally copies these two, and the generated C
              includes them, so they belong to the installable header set. *)
           (if Options.uses_pulse_api ()
            then [mk_filename "EverParsePulse" "h"; mk_filename "EverParsePulseEndianness" "h"]
            else [])
      else []
      end `List.Tot.append`
      begin if ext <> "h"
      then
        List.concatMap (fun f -> let m = Options.module_name f in if Deps.has_static_assertions g m then [mk_filename (Printf.sprintf "%sStaticAssertions" m) ext] else []) all_files
      else []
      end `List.Tot.append`
      List.concatMap (fun f -> let m = Options.module_name f in if Deps.has_entrypoint g m then [mk_filename (Printf.sprintf "%sWrapper" m) ext] else []) all_files `List.Tot.append`
      begin if ext <> "h"
      then
        List.concatMap (fun f ->
          let m = Options.module_name f in
          if Deps.has_out_exprs g m
          then [mk_filename (Printf.sprintf "%s_OutputTypes" m) ext]
          else []) all_files
      else []
      end `List.Tot.append`
      begin if ext = "h"
      then List.concatMap (fun f -> let m = Options.module_name f in maybe_h emit_output_types_defs g m) all_files
      else []
      end `List.Tot.append`
      List.map (fun f -> mk_filename (Options.module_name f) ext) all_files
    in
    FStar.IO.write_string file (Printf.sprintf "EVERPARSE_ALL_%s_FILES=%s\n" ext_cap (String.concat " " (List.Tot.map (mk_rule_operand mtype) ln)))
  in
  write_all_ext_files "H" "h";
  write_all_ext_files "C" "c";
  write_all_ext_files "O" (oext mtype);
  let cui_files = List.map (fun f -> mk_filename (Options.module_name f) "cui") all_files in
  FStar.IO.write_string file (Printf.sprintf "EVERPARSE_ALL_CUI_FILES=%s\n"
    (String.concat " " (List.Tot.map (mk_rule_operand mtype) cui_files)));
  if save_hashes then begin
    let json_files = List.map (fun f -> mk_filename (Options.module_name f) "json") all_files in
    FStar.IO.write_string file (Printf.sprintf "EVERPARSE_ALL_JSON_FILES=%s\n" (String.concat " " (List.Tot.map (mk_rule_operand mtype) json_files)))
  end;
  FStar.IO.close_write_file file;
  OS.rename makefile_tmp makefile_final
