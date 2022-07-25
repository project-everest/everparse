open Prims
let employee_test =
  fun b ->
    LowParse_Spec_Base.parse Employee.employee_parser b

type stream_reader = BatIO.input
let open_stdin () = BatIO.stdin
let read_line s =
  try
    Some (BatIO.read_line s)
  with
    _ -> None

let _ =
  let stdin = open_stdin () in
   match read_line stdin with
   | None -> print_string "Done"
   | Some line ->
      let s = String.to_seq line in
      let bs = Seq.fold_left (fun out ch -> Char.code ch :: out) [] s in
      match employee_test (FStar_Seq_Base.MkSeq (List.rev bs)) with
      | None -> print_string "Failed\n"
      | Some (et,n) ->
        print_string "Success: Salary is ";
        print_string (Stdint.Uint16.to_string et.Employee.salary);
        print_string "\n"
