module GenMakefile

type rule_t = {
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
    let rule = Printf.sprintf "%s\t$(EVERPARSE_CMD) --odir %s %s\n\n" rule output_dir r.args in
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
    from = types_fst :: List.Tot.map (fun m -> mk_filename m "Types.fst.checked") (Deps.dependencies g modul);
    to = [mk_filename modul "Types.fst.checked"];
    args = Printf.sprintf "--__micro_step verify %s" types_fst;
  }

let produce_fsti_checked_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
= let fsti = mk_filename modul "fsti" in
  {
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
    from = mk_filename modul "Types.fst.checked" :: List.Tot.map (fun m -> mk_filename m "Types.fst.checked") (Deps.dependencies g modul);
    to = [mk_filename (Printf.sprintf "%s_Types" modul) "krml"];
    args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "Types.fst");
  }

let produce_krml_rule
  (g: Deps.dep_graph)
  (modul: string)
: Tot rule_t
=
  {
    from = mk_filename modul "fst.checked" :: List.Tot.map (fun m -> mk_filename m "fst.checked") (Deps.dependencies g modul);
    to = [mk_filename modul "krml"];
    args = Printf.sprintf "--__micro_step extract %s" (mk_filename modul "fst");
  }

let produce_fst_rule
  (all_files: list string)
: FStar.All.ML rule_t
=
  {
    from = all_files;
    to =
      begin
        let types = List.map (fun f -> mk_filename (Options.get_module_name f) "Types.fst") all_files in
        let fsti = List.map (fun f -> mk_filename (Options.get_module_name f) "fsti") all_files in
        let fst = List.map (fun f -> mk_filename (Options.get_module_name f) "fst") all_files in
        types `List.Tot.append` fsti `List.Tot.append` fst
      end;
    args = Printf.sprintf "--__skip_deps --no_batch %s" (String.concat " " all_files);
  }

let produce_h_rule
  (all_files: list string)
: FStar.All.ML rule_t
=
  {
    from =
      List.map (fun f -> mk_filename (Options.get_module_name f) "krml") all_files `List.Tot.append`
      List.map (fun f -> mk_filename (Printf.sprintf "%s_Types" (Options.get_module_name f)) "krml") all_files
      ;
    to = List.map (fun f -> mk_filename (Options.get_module_name f) "h") all_files;
    args = Printf.sprintf "--__skip_deps --__produce_c_from_existing_krml %s" (String.concat " " all_files);
  }

let produce_makefile
  (files: list string)
: FStar.All.ML (list rule_t)
=
  let g = Deps.build_dep_graph_from_list files in
  let all_files = Deps.collect_and_sort_dependencies_from_graph g files in
  let all_modules = List.map Options.get_module_name all_files in
  produce_h_rule all_files ::
  produce_fst_rule all_files ::
  List.Tot.map (produce_types_checked_rule g) all_modules `List.Tot.append`
  List.Tot.map (produce_fsti_checked_rule g) all_modules `List.Tot.append`
  List.Tot.map (produce_fst_checked_rule g) all_modules `List.Tot.append`
  List.Tot.map (produce_types_krml_rule g) all_modules `List.Tot.append`
  List.Tot.map (produce_krml_rule g) all_modules

let write_gnu_makefile
  (files: list string)
: FStar.All.ML unit
=
  let makefile = Options.get_makefile_name () in
  let file = FStar.IO.open_write_file makefile in
  FStar.IO.write_string file (String.concat "" (List.Tot.map print_gnu_make_rule (produce_makefile files)));
  FStar.IO.close_write_file file
