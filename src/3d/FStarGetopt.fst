module FStarGetopt
let noshort = '\0'

let bind (l: parse_cmdline_res) (f: unit -> ML parse_cmdline_res) : ML parse_cmdline_res =
    match l with
    | Help
    | Error _ -> l
    | Success -> f ()
    (* | Empty  *)
    (* ^ Empty does not occur internally. *)

(* Returns None if this wasn't an option arg (did not start with "-")
 * Otherwise, returns Some (o, s) where [s] is the trimmed option, and [o]
 * is the opt we found in specs (possibly None if not present, which should
 * trigger an error) *)
let find_matching_opt specs s : ML (option (option opt * string)) =
  if String.length s < 2 then
    None
  else if String.sub s 0 2 = "--" then
    (* long opts *)
    let strim : string = String.sub s 2 ((String.length s) - 2) in
    let o = FStar.List.tryFind (fun (_, option, _) -> option = strim) specs in
    Some (o, strim)
  else if String.sub s 0 1 = "-" then
    (* short opts *)
    let strim : string = String.sub s 1 ((String.length s) - 1) in
    let o = FStar.List.tryFind (fun (shortoption, _, _) -> String.make 1 shortoption = strim) specs in
    Some (o, strim)
  else
    None

(* remark: doesn't work with files starting with -- *)
let rec parse (opts:list opt) (def: _ -> ML _) ar ix max i : ML parse_cmdline_res =
  if ix > max then Success
  else
    let arg = List.nth ar ix in
    let go_on () = bind (def arg) (fun _ -> parse opts def ar (ix + 1) max (i + 1)) in
    match find_matching_opt opts arg with
    | None -> go_on ()
    | Some (None, _) -> Error ("unrecognized option '" ^ arg ^ "'\n")
    | Some (Some (_, _, p), argtrim) ->
      begin match p with
      | ZeroArgs f -> f (); parse opts def ar (ix + 1) max (i + 1)
      | OneArg (f, _) ->
         if ix + 1 > max
         then Error ("last option '" ^ argtrim ^ "' takes an argument but has none\n")
         else
           let r =
               try (f (List.nth ar (ix + 1)); Success)
               with _ -> Error ("wrong argument given to option `" ^ argtrim ^ "`\n")
           in bind r (fun () -> parse opts def ar (ix + 2) max (i + 1))
      end

let parse_array specs others args offset =
  parse specs others args offset (List.length args - 1) 0

let parse_cmdline specs others =
  parse_array specs others (cmdline ()) 1

let parse_string specs others (str:string) =
    let split_spaces (str:string) =
      let seps = [' '; '\t'] in
      FStar.List.filter (fun s -> s <> "") (String.split seps str)
    in
    let index_of str c : Pure int
      (requires True)
      (ensures fun i -> i >= -1 /\ i < String.length str)
    =
        let res = String.index_of str c in
        if res < 0 || res >= String.length str then -1 else res
    in
    let substring_from s j =
        if j > String.length s then "" else
        let len = String.length s - j in
        (String.sub s j len <: string)
    in
    let rec split_quoted_fragments (str:string) : ML _ =
        let i = index_of str '\'' in
        if i < 0 then Some (split_spaces str)
        else let prefix = String.sub str 0 i in
             let suffix = substring_from str (i + 1) in
             let j = index_of suffix '\'' in
             if j < 0 then None
             else let quoted_frag = String.sub suffix 0 j in
                  let rest = split_quoted_fragments (substring_from suffix (j + 1)) in
                  match rest with
                  | None -> None
                  | Some rest -> Some (split_spaces prefix @ quoted_frag::rest)

    in
    match split_quoted_fragments str with
    | None -> Error("Failed to parse options; unmatched quote \"'\"")
    | Some args ->
      parse_array specs others args 0

let parse_list specs others lst =
  parse_array specs others lst 0
