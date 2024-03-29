type mode =
  | PrettyPrint
  | FStarOutput
  | OCamlOutput

let debug       = ref false
let ver         = "0.1"
let mode        = ref FStarOutput
let prefix      = ref ""
let bytes       = ref "FStar.Bytes"
let odir        = ref "."
let opt_none    = ref "None"
let opt_some    = ref "Some"
let opt_type    = ref "option"
let emit_high   = ref true
let emit_low    = ref true
let emit_eq     = ref false
let types_from  = ref ""
let types_to    = ref ""

let headers : (string list * string list) ref
  = ref ([], [])
