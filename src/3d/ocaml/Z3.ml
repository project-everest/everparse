open Z3_Base

let tee ch s =
  print_string s;
  output_string ch s;
  flush ch

let with_z3 (f: (z3 -> 'a)) : 'a =
  let (ch_from_z3, ch_to_z3) as ch_z3 = Unix.open_process "z3 -in" in
  let valid = ref true in
  let is_from = ref true in
  let from_z3 () : string =
    if !valid then begin
      if not !is_from
      then begin
        print_endline ";; From z3";
        is_from := true
      end;
      let s = input_line ch_from_z3 in
      print_endline s;
      s
    end
    else ""
  in
  let to_z3 (s: string) : unit =
    if !valid then begin
      if !is_from
      then begin
        print_endline ";; To z3";
        is_from := false
      end;
      tee ch_to_z3 s
    end
  in
  let z3 = {
    from_z3 = from_z3;
    to_z3 = to_z3;
  }
  in
  let res = f z3 in
  valid := false;
  let _ = Unix.close_process ch_z3 in
  res
