let string_of_byte a =
  let s = Printf.sprintf "%x" a in
  if a < 16
  then "0" ^ s
  else s

let rec string_of_all_bytes' accu n s i =
  if i >= n
  then accu
  else
    let a = FStar_Seq_Base.index s i in
    let accu' = accu ^ " " ^ string_of_byte a in
    string_of_all_bytes' accu' n s (Z.add i (Prims.of_int 1))

let string_of_all_bytes accu s =
  string_of_all_bytes' accu (FStar_Seq_Base.length s) s (Prims.of_int 0)

let parse_debug _ msg p input =
  let msg' = string_of_all_bytes msg input in
  print_endline ("STARTED: " ^ msg');
  let res = p input in
  let status = match res with
    | Some _ ->
       "SUCCESS: "
    | None ->
       "FAILURE: "
  in
  print_endline (status ^ msg');
  res

let parse_debugf _ msg fp x input =
  let msg' = string_of_all_bytes msg input in
  print_endline ("STARTED: " ^ msg');
  let res = fp x input in
  let status = match res with
    | Some _ ->
       "SUCCESS: "
    | None ->
       "FAILURE: "
  in
  print_endline (status ^ msg');
  res

let print_debug msg v =
  print_endline msg;
  v
