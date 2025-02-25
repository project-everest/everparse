open Z3_Base

let tee debug ch s =
  if debug then print_string s;
  output_string ch s;
  flush ch

let maybe_output_string (maybe_file: out_channel option) (s: string) =
  match maybe_file with
  | None -> ()
  | Some f -> output_string f s

let maybe_output_line (maybe_file: out_channel option) (s: string) =
  maybe_output_string maybe_file s;
  maybe_output_string maybe_file "\n"

let with_z3 (debug: bool) (transcript: string option) (f: (z3 -> 'a)) : 'a =
  let cmd_line = Printf.sprintf "%s %s -in" (Options.get_z3_executable ()) (Options.get_z3_options ()) in
  let (ch_from_z3, ch_to_z3) as ch_z3 = Unix.open_process cmd_line in
  let ch_transcript = match transcript with
    | None -> None
    | Some f -> Some (open_out f)
  in
  let valid = ref true in
  let is_from = ref true in
  let from_z3 () : string =
    if !valid then begin
      if not !is_from
      then begin
        if debug then print_endline ";; From z3";
        maybe_output_line ch_transcript ";; From z3";
        is_from := true
      end;
      let s = input_line ch_from_z3 in
      if debug then print_endline s;
      maybe_output_string ch_transcript "; ";
      maybe_output_line ch_transcript s;
      s
    end
    else ""
  in
  let to_z3 (s: string) : unit =
    if !valid then begin
      if !is_from
      then begin
        if debug then print_endline ";; To z3";
        maybe_output_line ch_transcript ";; To z3";
        is_from := false
      end;
      maybe_output_line ch_transcript s;
      tee debug ch_to_z3 s
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
  let _ = match ch_transcript with
    | None -> ()
    | Some f -> close_out f
  in
  res

type z3_thread = int

let with_z3_thread (debug: bool) (transcript: string option) (f: (z3 -> unit)) : z3_thread =
  let phi () = with_z3 debug transcript f in
  if Sys.win32
  then
    begin
      phi ();
      0
    end
  else
    begin
      let pid = Unix.fork () in
      if pid = 0
      then begin
          phi ();
          exit 0
        end
      else pid
    end
      
let wait_for_z3_thread pid =
  if Sys.win32
  then ()
  else
    begin
      print_endline "Waiting for Z3...";
      ignore (Unix.waitpid [] pid)
    end
