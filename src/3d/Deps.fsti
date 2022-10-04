module Deps

open FStar.All

val dep_graph : Type0

val dependencies (graph: dep_graph) (modul: string) : Tot (list string)

val build_dep_graph_from_list (files: list string) : ML dep_graph

val collect_and_sort_dependencies_from_graph (g: dep_graph) (files:list string) : ML (list string)

let collect_and_sort_dependencies (files:list string) : ML (list string) =
  collect_and_sort_dependencies_from_graph (build_dep_graph_from_list files) files

val has_entrypoint (g: dep_graph) (modul: string) : Tot bool

val has_static_assertions (g: dep_graph) (modul: string) : Tot bool

val has_output_types (g:dep_graph) (modul:string) : bool

val has_extern_types (g:dep_graph) (modul:string) : bool

val has_extern_functions (g:dep_graph) (modul:string) : bool

val get_config (_:unit) : ML (option (Config.config & string))
