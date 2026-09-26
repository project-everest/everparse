module Config
module O = Options
type compile_time_flags = {
  flags : list string;
  include_file : string;
}

type config = {
  compile_time_flags : compile_time_flags
}

(* Read by ocaml/Batch.ml, which cannot use the field directly: extraction is
   free to give a single-field record a representation of its own, and a
   hand-written .ml is not regenerated when it changes. *)
let config_compile_time_flags (c:config) : compile_time_flags =
  c.compile_time_flags

let emit_config_as_fstar_module (module_name:string) (c:config) = 
  let flags = 
    List.map 
      (Printf.sprintf "[@@ CIfDef]\nassume\nval ___%s : bool" )
      c.compile_time_flags.flags
  in
  let assumes = String.concat "\n\n" flags in
  Printf.sprintf "module %s\n%s\n" module_name assumes
