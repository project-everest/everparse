module JSON
open FStar.All
val prog_to_json (d:Ast.prog) : ML string
val config_to_json (c:Config.config) : ML string
val config_of_json (s:string) : ML (either Config.config string)
