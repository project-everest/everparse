open Ast
let prog_to_json (p:prog)
  : string
  = let yj = Ast.prog_to_yojson p in
    Yojson.Safe.to_string yj

let config_to_json (c:Config.config)
  : string
  = let yj = Config.config_to_yojson c in
    Yojson.Safe.to_string yj

let config_of_json (s:string)
  : (Config.config, string) FStar_Pervasives.either
  = try
      match Config.config_of_yojson (Yojson.Safe.from_string s) with
      | Result.Ok c -> FStar_Pervasives.Inl c
      | Result.Error s -> FStar_Pervasives.Inr s
    with Yojson.Json_error msg -> FStar_Pervasives.Inr msg
