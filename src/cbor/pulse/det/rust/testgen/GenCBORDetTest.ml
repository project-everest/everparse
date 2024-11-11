type rust = [
  | `Block of rust list
  | `FunDecl of string
  | `Instr of string
]

let instr_assert (s: string) : rust =
  `Instr ("assert!(" ^ s ^ ")")

let gen_int (x: int) (name: string) : rust list =
  let major_type, count =
    if x >= 0
    then ("uint64", x)
    else ("neg_int64", -1-x)
  in
  [`Instr ("let " ^ name ^ " : cbor_raw = cbor_det_mk_int64(cbor_major_type_" ^ major_type ^ "," ^ string_of_int count ^ ")")]

let quote_string s = Yojson.Safe.to_string (`String s)

let gen_string (s: string) (name: string) : rust list =
  [`Instr ("let " ^ name ^ " : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes(" ^ quote_string s ^ "))")]

let gen_map (gen: Yojson.Safe.t -> string -> rust list) (l: (string * Yojson.Safe.t) list) (name: string) : rust list =
  let len = List.length l in
  let elt i = name ^ "_map[" ^ string_of_int i ^ "]" in
  let accu = [`Instr ("let " ^ name ^ " : cbor_raw = cbor_det_mk_map(& mut " ^ name ^ "_map[..])")] in
  let rec aux accu i = function
  | [] -> accu
  | (s, x) :: q->
    let key_name = name ^ "_map_" ^ string_of_int i ^ "_key" in
    let value_name = name ^ "_map_" ^ string_of_int i ^ "_value" in
    let accu' =
      gen_string s key_name @
      gen x value_name @
      `Instr (elt i ^ " = cbor_map_entry {cbor_map_entry_key: " ^ key_name ^ ", cbor_map_entry_value: " ^ value_name ^ "}") ::
      accu
    in
    aux accu' (i + 1) q
  in
  let accu' = aux accu 0 l in
  let accu' = `Instr ("let mut " ^ name ^ "_map: [cbor_map_entry; " ^ string_of_int len ^ " ] = [dummy_cbor_map_entry; " ^ string_of_int len ^ "]") :: accu' in
  accu'

let gen_array (gen: Yojson.Safe.t -> string -> rust list) (l: Yojson.Safe.t list) (name: string) : rust list =
  let len = List.length l in
  let elt i = name ^ "_array[" ^ string_of_int i ^ "]" in
  let accu = [`Instr ("let " ^ name ^ " : cbor_raw = cbor_det_mk_array(&" ^ name ^ "_array[..])")] in
  let rec aux accu i = function
  | [] -> accu
  | x :: q->
    let value_name = name ^ "_array_" ^ string_of_int i in
    let accu' =
      gen x value_name @
      `Instr (elt i ^ " = " ^ value_name) ::
      accu
    in
    aux accu' (i + 1) q
  in
  let accu' = aux accu 0 l in
  let accu' = `Instr ("let mut " ^ name ^ "_array: [cbor_raw; " ^ string_of_int len ^ " ] = [dummy_cbor; " ^ string_of_int len ^ "]") :: accu' in
  accu'

exception GenUnsupported

let rec gen (x: Yojson.Safe.t) (name: string) : rust list =
  match x with
  | `Int x -> gen_int x name
  | `String x -> gen_string x name
  | `Assoc x -> gen_map gen x name
  | `List x -> gen_array gen x name
  | _ -> raise GenUnsupported

let gen_hex (l: string) (name: string) : int * string =
  let len = String.length l in
  let (l, len) =
    if len mod 2 = 0
    then (l, len)
    else ("0" ^ l, 1 + len)
  in
  let count = len / 2 in
  let accu = "let " ^ name ^ ": [u8; " ^ string_of_int count ^ "] = [" in
  let rec aux accu x =
    if x = len
    then accu
    else if x = len - 2
    then accu ^ "0x" ^ String.sub l x 2
    else
      let accu' = accu ^ "0x" ^ String.sub l x 2 ^ ", " in
      aux accu' (x + 2)
  in
  (count, aux accu 0 ^ "]")

let list_assoc x l =
  try
    Some (List.assoc x l)
  with Not_found -> None

let gen_encoding_test_c
  (count: int)
  (num: int ref)
  (item: Yojson.Safe.t * string * (rust list))
: rust list
= num := !num + 1;
  let (decoded, hex_encoded, decoded_c) = item in
  let decoded_s = quote_string (Yojson.Safe.to_string decoded) in
  let (size, source_bytes) = gen_hex hex_encoded "source_bytes" in
  let size_s = string_of_int size in
  `FunDecl("#[allow(unused_variables)]") ::
  `FunDecl("#[test]") ::
  `FunDecl("fn test" ^ string_of_int !num ^ "()") ::
  `Block (
    `Instr ("let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0)") ::
    `Instr ("let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor }") ::
    `Instr source_bytes ::
    `Instr ("let source_bytes = &source_bytes[..]") ::
    decoded_c @
    `Instr ("let mut target_bytes: [u8; " ^ size_s ^ "] = [0xff; " ^ size_s ^ "]") ::
    `Instr ("let mut target_byte_size: usize = cbor_det_size(source_cbor, " ^ size_s ^ ")") ::
    instr_assert ("target_byte_size == " ^ size_s) ::
    `Instr ("target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..])") ::
    instr_assert ("target_byte_size == " ^ size_s) ::
    instr_assert ("&target_bytes[0.." ^ size_s ^ "] == source_bytes") ::
    `Instr ("target_byte_size = cbor_det_validate(source_bytes)") ::
    instr_assert ("target_byte_size == " ^ size_s) ::
    `Instr ("let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size)") ::
    instr_assert ("cbor_det_equal(source_cbor, target_cbor)") ::
    []
  ) ::
  []

let extract_encoding_test
  (item0: Yojson.Safe.t)
: Yojson.Safe.t * string * rust list
=
match item0 with
| `Assoc item -> 
  begin match list_assoc "roundtrip" item with
  | Some (`Bool true) ->
     begin match list_assoc "decoded" item with
     | Some decoded ->
        begin match list_assoc "hex" item with
        | Some (`String hex) ->
          begin try
              (decoded, hex, gen decoded "source_cbor")
          with GenUnsupported -> begin
              prerr_endline ("skipping unsupported encoding test: " ^ Yojson.Safe.to_string item0);
              (decoded, "", [])
              end
          end
        | _ -> failwith ("Not a valid test case assoc (hex):" ^ Yojson.Safe.to_string item0)
        end
     | None ->
        prerr_endline ("skipping no-decoded test case: " ^ Yojson.Safe.to_string item0);
        (item0, "", [])
     end
  | Some (`Bool false) ->
     prerr_endline ("skipping non-roundtrip test case: " ^ Yojson.Safe.to_string item0);
     (item0, "", [])
  | _ ->
     failwith ("Not a valid test case assoc (roundtrip): " ^ Yojson.Safe.to_string item0)
  end
| _ -> failwith ("Not a valid test case (expected map): " ^ Yojson.Safe.to_string item0)

let gen_encoding_tests
  (x: Yojson.Safe.t)
: rust list
= match x with
  | `List items ->
     let l = List.map extract_encoding_test items in
     let len = List.length l in
     let l' = List.filter (function (_, _, []) -> false | _ -> true) l in
     let len' = List.length l' in
     prerr_endline (string_of_int len' ^ " tests supported out of a total " ^ string_of_int len);
     let num = ref 0 in
     List.flatten (List.map (gen_encoding_test_c len' num) l')
  | _ -> failwith ("Not a valid test suite: (expected array): " ^ Yojson.Safe.to_string x)

let rec rust_to_string
  (indent: string)
  (x: rust)
: string
= match x with
  | `FunDecl x -> indent ^ x ^ "\n"
  | `Instr x -> indent ^ x ^ ";\n"
  | `Block x -> indent ^ "{\n" ^ rust_list_to_string (indent ^ "  ") "" x ^ indent ^ "}\n"

and rust_list_to_string
  (indent: string)
  (accu: string)
  (l: rust list)
= match l with
  | [] -> accu
  | a :: q -> rust_list_to_string indent (accu ^ rust_to_string indent a) q

let mk_prog (x: rust list) = "
use cborrs::cbordet::*;


"
  ^ rust_list_to_string "" "" x

let _ =
  let rec aux accu i =
    if i = Array.length Sys.argv
    then accu
    else
      let accu' = accu @ gen_encoding_tests (Yojson.Safe.from_file Sys.argv.(i)) in
      aux accu' (i + 1)
  in
  let body = aux [] 1 in (* skip argv[0] *)
  let prog = mk_prog body in
  print_endline prog
