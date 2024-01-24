open Hashing_Hash

(* load, check and save weak hashes from a C file *)

let check_inplace_hashes file_3d files_c =
  let f h file_c =
    let ch = open_in file_c in
    (* Check fails if a bad hash or no hash is found. A
       good hash alone does not make the check succeed *)
    let rec aux accu =
      try
        let l = input_line ch in
        begin match String.split_on_char ':' (String.trim l) with
        | [hd; tl] when hd = c_comment_intro ->
           if tl = h
           then aux true
           else begin
               Printf.printf "Weak hash check failed in %s, expected %s, found %s\n" file_c h tl;
               false
           end 
        | _ -> aux accu
        end
      with End_of_file -> 
        begin
          if not accu
          then Printf.printf "No hash found in %s\n" file_c;
          accu
        end
    in
    let res = aux false in
    close_in ch;
    res
  in
  Hashing_Hash.check_inplace_hashes f file_3d files_c

(* load, check and save hashes from/to JSON file *)

let load_hash file is_weak =
  try
    begin match Yojson.Basic.from_file file with
    | `Assoc l ->
       let name = Printf.sprintf "%s-hash" (if is_weak then "weak" else "strong") in
       begin match List.assoc_opt name l with
       | Some (`String s) -> Some s
       | _ -> None
       end
    | _ -> None
    end
  with _ -> None

let check_hash f opt_c f_json =
  match load_hash f_json (opt_c = None) with
  | None ->
     Printf.printf "No hashes found for %s\n" f;
     false
  | Some h0 ->
     let h = hash f opt_c in
     let res = (h0 = h) in
     if not res
     then Printf.printf "%s hash check failed for %s\nOriginal: %s\nComputed: %s\n" (if opt_c = None then "weak" else "strong") f h0 h;
     res

let save_hashes f opt_c f_json =
  let weak_hash = hash f None in
  let l : (string * Yojson.Basic.t) list = [("weak-hash", `String weak_hash)] in
  let l : (string * Yojson.Basic.t) list = match opt_c with
    | None -> l
    | _ ->
       let strong_hash = hash f opt_c in
       ("strong-hash", `String strong_hash) :: l
  in
  Yojson.Basic.to_file f_json (`Assoc l)
