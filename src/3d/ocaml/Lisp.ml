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
  | _ -> failwith "parse_seq_int_expr: unrecognized function call"

let parse_witness = function
  | Sexplib.Sexp.List [Sexplib.Sexp.List [Sexplib.Sexp.Atom "witness"; w]] ->
    parse_seq_int_expr w
  | _ -> failwith "parse_witness: unrecognized witness"

let read_witness_from (from: unit -> string) =
  let (letbinding, sexp) = read_lisp_from from in
  let witness = parse_witness sexp in
  print_string ";; witness: [";
  List.iter (fun i -> print_string (Prims.to_string i); print_string "; ") witness;
  print_endline "]";
  (letbinding, FStar_Seq_Properties.seq_of_list witness)
