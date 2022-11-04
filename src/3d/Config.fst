module Config
module O = Options
[@@ PpxDerivingYoJson]
type compile_time_flags = {
  flags : list string;
  include_file : string;
}

[@@ PpxDerivingYoJson]
type config = {
  compile_time_flags : compile_time_flags
}

let emit_config_as_fstar_module (module_name:string) (c:config) = 
  let flags = 
    List.map 
      (Printf.sprintf "[@@ CIfDef]\nassume\nval ___%s : bool" )
      c.compile_time_flags.flags
  in
  let assumes = String.concat "\n\n" flags in
  Printf.sprintf "module %s\n%s\n" module_name assumes
