module GenMakefile
module OS = OS

type rule_type =
  | EverParse
  | CC

type rule_t = {
  ty: rule_type;
  from: list string;
  to: list string;
  args: string;
}

let output_dir = "$(EVERPARSE_OUTPUT_DIR)"

let print_gnu_make_rule
  (r: rule_t)
: Tot string
= (* NOTE: I could use multiple target rule &: from https://www.gnu.org/software/make/manual/html_node/Multiple-Targets.html,
     but that feature is too recent (GNU Make 4.3, February 2020)
   *)
  match r.to with
  | [] -> ""
  | a :: q ->
    let rule = Printf.sprintf "%s : %s\n" a (String.concat " " r.from) in
    let cmd =
      match r.ty with
      | EverParse -> Printf.sprintf "$(EVERPARSE_CMD) --odir %s" output_dir
      | CC -> Printf.sprintf "$(CC) -I %s -c" ("$(EVERPARSE_HOME)" `OS.concat` "src" `OS.concat` "3d")
    in
    let rule = Printf.sprintf "%s\t%s %s\n\n" rule cmd r.args in
    let rule = List.Tot.fold_left (fun rule ne -> Printf.sprintf "%s%s: %s\n\ttest -f $@ && touch $@\n\n" rule ne a) rule q in
    rule

let mk_filename
  (modul: string)
  (ext: string)
: Tot string
= (Printf.sprintf "%s.%s" modul ext)

let produce_types_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
= let types_fst = mk_filename modul "Types.fst" in 
  {
    ty = EverParse;
    from = types_fst :: List.Tot.map (fun m -> mk_filename m "fsti.checked") (Deps.dependencies g modul);
    to = [mk_filename modul "Types.fst.checked"];
    args = Printf.sprintf "--__micro_step verify %s" types_fst;
  }

let produce_fsti_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
= let fsti = mk_filename modul "fsti" in
  {
    ty = EverParse;
    from = fsti :: mk_filename modul "Types.fst.checked" :: List.Tot.map (fun m -> mk_filename m "fsti.checked") (Deps.dependencies g modul);
    to = [mk_filename modul "fsti.checked"];
    args = Printf.sprintf "--__micro_step verify %s" fsti;
  }

let produce_fst_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
= let fst = mk_filename modul "fst" in
  {
    ty = EverParse;
    from = fst :: mk_filename modul "fsti.checked" :: List.Tot.map (fun m -> mk_filename m "fsti.checked") (Deps.dependencies g modul);
    to = [mk_filename modul "fst.checked"];
    args = Printf.sprintf "--__micro_step verify %s" fst;
  }

let produce_types_krml_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
=
  {
    ty = EverParse;
    from = mk_filename modul "Types.fst.checked" :: List.Tot.map (fun m -> mk_filename m "fst.checked") (Deps.dependencies g modul);
    to = [mk_filename (Printf.sprintf "%s_Types" modul) "krml"];
    args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "Types.fst");
  }

let produce_krml_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
=
  {
    ty = EverParse;
    from = mk_filename modul "fst.checked" :: List.Tot.map (fun m -> mk_filename m "fst.checked") (Deps.dependencies g modul);
    to = [mk_filename modul "krml"];
    args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "fst");
  }

let produce_fst_rule
  (all_files: list string)
: FStar.All.ML rule_t
=
  {
    ty = EverParse;
    from = all_files;
    to =
      begin
        let types = List.map (fun f -> mk_filename (Options.get_module_name f) "Types.fst") all_files in
        let fsti = List.map (fun f -> mk_filename (Options.get_module_name f) "fsti") all_files in
        let fst = List.map (fun f -> mk_filename (Options.get_module_name f) "fst") all_files in
        let wrapper_h = List.map (fun f -> mk_filename (Printf.sprintf "%sWrapper" (Options.get_module_name f)) "h") all_files in
        let wrapper_c = List.map (fun f -> mk_filename (Printf.sprintf "%sWrapper" (Options.get_module_name f)) "c") all_files in
        types `List.Tot.append` fsti `List.Tot.append` fst `List.Tot.append` wrapper_h `List.Tot.append` wrapper_c
      end;
    args = Printf.sprintf "--__skip_deps --no_batch %s" (String.concat " " all_files);
  }

let produce_h_rule
  (g: Deps.dep_graph)
  (file: string)
: FStar.All.ML rule_t
=
  let all_files = Deps.collect_and_sort_dependencies_from_graph g [file] in
  {
    ty = EverParse;
    from =
      List.map (fun f -> mk_filename (Options.get_module_name f) "krml") all_files `List.Tot.append`
      List.map (fun f -> mk_filename (Printf.sprintf "%s_Types" (Options.get_module_name f)) "krml") all_files
      ;
    to = [mk_filename (Options.get_module_name file) "h"; mk_filename (Options.get_module_name file) "c"];
    args = Printf.sprintf "--__produce_c_from_existing_krml %s" file;
  }

let produce_o_rule
  (modul: string)
: Tot rule_t
=
  let c = mk_filename modul "c" in
  {
    ty = CC;
    from = [c; mk_filename modul "h"];
    to = [mk_filename modul "o"];
    args = c;
  }

let produce_wrapper_o_rule
  (modul: string)
: Tot rule_t
=
  let wc = mk_filename (Printf.sprintf "%sWrapper" modul) "c" in
  let wh = mk_filename (Printf.sprintf "%sWrapper" modul) "h" in
  let wo = mk_filename (Printf.sprintf "%sWrapper" modul) "o" in
  let h = mk_filename modul "h" in
  {
    ty = CC;
    from = [wc; wh; h];
    to = [wo];
    args = wc;
  }

let produce_makefile
  (files: list string)
: FStar.All.ML (list rule_t & list string)
=
  let g = Deps.build_dep_graph_from_list files in
  let all_files = Deps.collect_and_sort_dependencies_from_graph g files in
  let all_modules = List.map Options.get_module_name all_files in
  let rules =
    produce_fst_rule all_files ::
    List.Tot.map (produce_types_checked_rule g) all_modules `List.Tot.append`
    List.Tot.map (produce_fsti_checked_rule g) all_modules `List.Tot.append`
    List.Tot.map (produce_fst_checked_rule g) all_modules `List.Tot.append`
    List.Tot.map (produce_types_krml_rule g) all_modules `List.Tot.append`
    List.Tot.map (produce_krml_rule g) all_modules `List.Tot.append`
    List.map (produce_h_rule g) all_files `List.Tot.append`
    List.Tot.map produce_o_rule all_modules `List.Tot.append`
    List.Tot.map produce_wrapper_o_rule all_modules
  in
  (rules, all_files)

let write_gnu_makefile
  (files: list string)
: FStar.All.ML unit
=
  let makefile = Options.get_makefile_name () in
  let file = FStar.IO.open_write_file makefile in
  let (rules, all_files) = produce_makefile files in
  FStar.IO.write_string file (String.concat "" (List.Tot.map print_gnu_make_rule rules));
  let write_all_ext_files (ext_cap: string) (ext: string) : FStar.All.ML unit =
    let ln =
      List.map (fun f -> mk_filename (Options.get_module_name f) ext) all_files `List.Tot.append`
      List.map (fun f -> mk_filename (Printf.sprintf "%sWrapper" (Options.get_module_name f)) ext) all_files
    in
    FStar.IO.write_string file (Printf.sprintf "ALL_%s_FILES=%s\n" ext_cap (String.concat " " ln))
  in
  write_all_ext_files "H" "h";
  write_all_ext_files "C" "c";
  write_all_ext_files "O" "o";
  FStar.IO.close_write_file file
