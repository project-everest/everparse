type mode =
  | PrettyPrint
  | FStarOutput
  | OCamlOutput

let debug       = ref false
let ver         = "0.1"
let mode        = ref FStarOutput
let prefix      = ref "Parse_"
let bytes       = ref "FStar.Bytes"
let odir        = ref "."
let opt_none    = ref "None"
let opt_some    = ref "Some"
let opt_type    = ref "option"

let headers : (string list * string list) ref
  = ref ([], [])
