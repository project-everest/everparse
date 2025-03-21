module GenMakefile
module OS = OS

type rule_type =
  | EverParse
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
  (r: rule_t)
: Tot string
= 
  let rule = Printf.sprintf "%s : %s\n" (mk_rule_operand mtype r.to) (String.concat " " (List.Tot.map (mk_rule_operand mtype) r.from)) in
  match r.ty with
  | Nop -> Printf.sprintf "%s\n" rule
  | _ ->
    let cmd =
      match r.ty with
      | EverParse -> Printf.sprintf "$(EVERPARSE_CMD) --odir %s" output_dir
      | CC ->
        let iopt = match mtype with
          | HashingOptions.MakefileGMake -> "-I"
          | HashingOptions.MakefileNMake -> "/I"
        in
        let inc =
          if everparse_h
          then ""
          else
            let ddd_home = "$(EVERPARSE_HOME)" `OS.concat` "src" `OS.concat` "3d" in
            let ddd_actions_home = ddd_home `OS.concat` "prelude" `OS.concat` (HashingOptions.string_of_input_stream_binding input_stream_binding) in
            Printf.sprintf "%s %s %s %s" iopt ddd_home iopt ddd_actions_home
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
    let krml_file_name = mk_filename module_name "krml" in
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
    let krml_rule = {
      ty = EverParse;
      from = [checked_file_name];
      to =  krml_file_name;
      args = Printf.sprintf "--__micro_step extract %s" fst_file_name;        
    } in
    [fst_rule; fst_checked_rule; krml_rule]
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

let produce_external_types_krml_rule
  (g: Deps.dep_graph)
  (modul: string)
: list rule_t
= if not (has_external_types_fsti g modul) then []
  else
    let external_types_fsti_checked = mk_filename modul "ExternalTypes.fsti.checked" in 
    [{
       ty = EverParse;
       from = external_types_fsti_checked :: List.Tot.map (fun m -> mk_filename m "fst.checked") (Deps.dependencies g modul);
       to = mk_filename (Printf.sprintf "%s_ExternalTypes" modul) "krml";
       args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "ExternalTypes.fsti");
     }]

let produce_external_api_krml_rule
  (g: Deps.dep_graph)
  (modul: string)
: list rule_t
= if not (has_external_api_fsti g modul) then []
  else
    let external_api_fsti_checked = mk_filename modul "ExternalAPI.fsti.checked" in 
    [{
       ty = EverParse;
       from = external_api_fsti_checked :: List.Tot.map (fun m -> mk_filename m "fst.checked") (Deps.dependencies g modul);
       to = mk_filename (Printf.sprintf "%s_ExternalAPI" modul) "krml";
       args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "ExternalAPI.fsti");
     }]

let produce_krml_rule
  (g: Deps.dep_graph)
  (modul: string)
: FStar.All.ML rule_t
=
  {
    ty = EverParse;
    from = add_cfg_file_dep "fst.checked" 
            (mk_filename modul "fst.checked" :: 
              List.Tot.map (fun m -> mk_filename m "fst.checked") (Deps.dependencies g modul));
    to = mk_filename modul "krml";
    args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "fst");
  }

let produce_nop_rule
  (from: list string)
  (to: string)
: Tot rule_t
=
  {
    ty = Nop;
    from = from;
    to = to;
    args = "";
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
  let modul = Options.get_module_name file in
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
      ty = EverParse;
      from =
        (if clang_format then [mk_filename "" "clang-format"] else []) `List.Tot.append`
        (if OS.file_exists (Printf.sprintf "%s.copyright.txt" file) then [mk_input_filename (Printf.sprintf "%s.copyright.txt" file)] else []) `List.Tot.append`
        [mk_input_filename file];
      to = first_fst;
      args = Printf.sprintf "--no_batch %s" (mk_input_filename file);
    } ::
    List.Tot.map (produce_nop_rule [first_fst]) (other_fst `List.Tot.append` produced_c)

let maybe_external_api_krml
  (g: Deps.dep_graph)
  (m: string)
: Tot (list string)
= if has_external_api_fsti g m
  then [mk_filename (Printf.sprintf "%s_ExternalAPI" m) "krml"]
  else []

let maybe_external_types_krml
  (g: Deps.dep_graph)
  (m: string)
: Tot (list string)
= if has_external_types_fsti g m
  then [mk_filename (Printf.sprintf "%s_ExternalTypes" m) "krml"]
  else []

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

let maybe_krml_generated_h
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
= maybe_krml_generated_h g m `List.Tot.append`
  maybe_external_typedefs_h emit_output_types_defs g m

let produce_h_rules
  (g: Deps.dep_graph)
  (clang_format: bool)
  (file: string)
: FStar.All.ML (list rule_t)
=
  let all_files = Deps.collect_and_sort_dependencies_from_graph g [file] in
  let to = mk_filename (Options.get_module_name file) "c" in
  let copyright = mk_input_filename (Printf.sprintf "%s.3d.copyright.txt" (Options.get_module_name file)) in
  {
    ty = EverParse;
    from =
      add_cfg_file_dep "krml" (
        (if clang_format then [mk_filename "" "clang-format"] else []) `List.Tot.append`
        (if OS.file_exists (Printf.sprintf "%s.copyright.txt" file) then [copyright] else []) `List.Tot.append`
        List.map (fun f -> mk_filename (Options.get_module_name f) "krml") all_files `List.Tot.append`
        List.concatMap (fun f ->
          let m = Options.get_module_name f in
          maybe_external_api_krml g m `List.Tot.append`
          maybe_external_types_krml g m
        ) all_files
      )
      ;
    to = to; (* IMPORTANT: relies on the fact that KaRaMeL generates .c files BEFORE .h files *)
    args = Printf.sprintf "--__produce_c_from_existing_krml %s" (mk_input_filename file);
  } ::
  produce_nop_rule [to] (mk_filename (Options.get_module_name file) "h") ::
  List.concatMap (fun f ->
    let m = Options.get_module_name f in
    List.Tot.map (produce_nop_rule [to]) (maybe_krml_generated_h g m)
  ) all_files

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
: Tot (list rule_t)
=
  if clang_format
  then [{
   ty = EverParse;
   from = [];
   to = mk_filename "" "clang-format";
   args = "--__micro_step copy_clang_format";
  }] else []

let produce_everparse_h_rule
  (everparse_h: bool)
: Tot (list rule_t)
=
  if everparse_h
  then [
    {
      ty = EverParse;
      from = [];
      to = mk_filename "EverParseEndianness" "h";
      args = "--__micro_step copy_everparse_h";
    };
    {
      ty = Nop;
      from = [mk_filename "EverParseEndianness" "h"];
      to = mk_filename "EverParse" "h";
      args = "";
    }
  ] else []

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
  (files: list string)
: FStar.All.ML produce_makefile_res
=
  let g = Deps.build_dep_graph_from_list files in
  let all_files = Deps.collect_and_sort_dependencies_from_graph g files in
  let all_modules = List.map Options.get_module_name all_files in
  let rules =
    produce_everparse_h_rule everparse_h `List.Tot.append`
    produce_clang_format_rule clang_format `List.Tot.append`
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
    List.Tot.concatMap (produce_external_types_krml_rule g) all_modules `List.Tot.append`
    List.Tot.concatMap (produce_external_api_krml_rule g) all_modules `List.Tot.append`
    List.map (produce_krml_rule g) all_modules `List.Tot.append`
    List.concatMap (produce_h_rules g clang_format) all_files `List.Tot.append`
    produce_config_fst_file_rule ()
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
  (files: list string)
: FStar.All.ML unit
=
  let makefile_final = Options.get_makefile_name () in
  let makefile_tmp = makefile_final ^ ".tmp" in
  let file = FStar.IO.open_write_file makefile_tmp in
  let {graph = g; rules; all_files} = produce_makefile mtype everparse_h emit_output_types_defs skip_o_rules clang_format files in
  FStar.IO.write_string file (String.concat "" (List.Tot.map (print_make_rule mtype everparse_h input_stream_binding) rules));
  let write_all_ext_files (ext_cap: string) (ext: string) : FStar.All.ML unit =
    let ln =
      begin if ext = "h" && everparse_h
      then [mk_filename "EverParse" "h"; mk_filename "EverParseEndianness" "h"]
      else []
      end `List.Tot.append`
      begin if ext <> "h"
      then
        List.concatMap (fun f -> let m = Options.get_module_name f in if Deps.has_static_assertions g m then [mk_filename (Printf.sprintf "%sStaticAssertions" m) ext] else []) all_files
      else []
      end `List.Tot.append`
      List.concatMap (fun f -> let m = Options.get_module_name f in if Deps.has_entrypoint g m then [mk_filename (Printf.sprintf "%sWrapper" m) ext] else []) all_files `List.Tot.append`
      begin if ext <> "h"
      then
        List.concatMap (fun f ->
          let m = Options.get_module_name f in
          if Deps.has_out_exprs g m
          then [mk_filename (Printf.sprintf "%s_OutputTypes" m) ext]
          else []) all_files
      else []
      end `List.Tot.append`
      begin if ext = "h"
      then List.concatMap (fun f -> let m = Options.get_module_name f in maybe_h emit_output_types_defs g m) all_files
      else []
      end `List.Tot.append`
      List.map (fun f -> mk_filename (Options.get_module_name f) ext) all_files
    in
    FStar.IO.write_string file (Printf.sprintf "EVERPARSE_ALL_%s_FILES=%s\n" ext_cap (String.concat " " (List.Tot.map (mk_rule_operand mtype) ln)))
  in
  write_all_ext_files "H" "h";
  write_all_ext_files "C" "c";
  write_all_ext_files "O" (oext mtype);
  FStar.IO.close_write_file file;
  OS.rename makefile_tmp makefile_final
