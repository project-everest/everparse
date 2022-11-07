module JSON
val prog_to_json (d:Ast.prog) : string
val config_to_json (c:Config.config) : string
val config_of_json (s:string) : either Config.config string
