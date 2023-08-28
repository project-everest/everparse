let read_lisp_from ch =
  let rec aux accu =
    let s = ch () in
    let accu' = accu ^ s in
    match Sexplib.Sexp.parse accu' with
    | Sexplib.Sexp.Done (res, _) -> (accu', res)
    | _ -> aux accu' (* FIXME: leverage incrementality instead of starting over *)
  in
  aux ""

let rec parse_seq_int_expr = function
  | Sexplib.Sexp.List (Sexplib.Sexp.Atom "seq.++" :: l) ->
    List.concat_map parse_seq_int_expr l
  | Sexplib.Sexp.List [Sexplib.Sexp.Atom "seq.unit"; Sexplib.Sexp.Atom n] ->
    [Prims.parse_int n]
  | Sexplib.Sexp.List [Sexplib.Sexp.Atom "as"; Sexplib.Sexp.Atom "seq.empty"; _] ->
    []
  | _ -> failwith "parse_seq_int_expr: unrecognized function call"

let parse_witness = function
  | Sexplib.Sexp.List [Sexplib.Sexp.List [Sexplib.Sexp.Atom "witness"; w]] ->
    parse_seq_int_expr w
  | _ -> failwith "parse_witness: unrecognized witness"

let parse_any (name: string) = function
  | Sexplib.Sexp.List [Sexplib.Sexp.List [Sexplib.Sexp.Atom name'; Sexplib.Sexp.Atom n]]
    when name = name' ->
    n
  | _ -> failwith ("parse_any: "^name^" not found")

let parse_int (name: string) sexp = Prims.parse_int (parse_any name sexp)

let read_int_from (from: unit -> string) (name: string) =
  let (letbinding, sexp) = read_lisp_from from in
  (letbinding, parse_int name sexp)

let read_bare_int_from (from: unit -> string) =
  Prims.parse_int (from ())

let read_any_from (from: unit -> string) (name: string) : string =
  parse_any name (snd (read_lisp_from from))
