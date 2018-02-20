open Globals
open Lexing
open Format
open Printf

open Rfc_ast
open Rfc_lexer
open Rfc_pretty
open Rfc_fstar_compiler
open Rfc_ocaml_compiler

let ifile : (string list) ref = ref []

let print_position outx lexbuf =
	let pos = lexbuf.lex_curr_p in
	fprintf outx "%s:%d:%d" pos.pos_fname
	pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let string_of_pos lexbuf =
	let s = lexbuf.lex_start_p in
	let c = lexbuf.lex_curr_p in
	sprintf "%s(%d,%d)-%s(%d,%d)" s.pos_fname s.pos_lnum (s.pos_cnum-s.pos_bol) c.pos_fname c.pos_lnum (c.pos_cnum-c.pos_bol)

let lexbuf_from_file filename =
	let channel = open_in filename in
	let lexbuf = Lexing.from_channel channel in
	lexbuf.lex_curr_p <- {
		lexbuf.lex_curr_p with
		pos_fname = filename;
		pos_bol = 1;
		pos_lnum = 1;
	};
	lexbuf

let rfc_tokenizer lb =
	let x = Rfc_lexer.read lb in
	if (!debug) then (BatPervasives.(print_any stdout x); printf "\n");
	x

let rfc_pretty ast =
	let p = rfc_pretty_print ast in
	print_endline p

let rfc_fstar ast =
	rfc_generate_fstar ast

let rfc_ocaml ast =
  failwith "OCaml compiler is currently disabled"
(*
	let p = rfc_generate_ocaml !module_name ast in
	print_endline p
*)

let rfc_load filename =
	let lexbuf =
		try lexbuf_from_file filename
		with | _ -> failwith ("failed to load file: "^filename) in
	let ast =
		try Rfc_parser.prog rfc_tokenizer lexbuf
		with
		| Rfc_parser.Error -> eprintf
			"Parsing error near %s\n" (string_of_pos lexbuf); exit 1
		| Rfc_lexer.SyntaxError s -> eprintf
			"Lexing error near %s: %s\n" (string_of_pos lexbuf) s; exit 1 in
	if (!debug) then (
		(print_endline " ");
		BatPervasives.(print_any stdout ast)
	);
	match !mode with
  | PrettyPrint -> rfc_pretty ast
	| FStarOutput -> rfc_fstar ast
	| OCamlOutput -> rfc_ocaml ast

let _ = Arg.parse [
	("-d", Arg.Unit (fun () -> debug := true),
		"enable debug output");

	("-pretty", Arg.Unit (fun () -> mode := PrettyPrint),
		"Pretty-print input specification");

	("-fstar",  Arg.Unit (fun () -> mode := FStarOutput),
		"Generate FStar code");

	("-ocaml",  Arg.Unit (fun () -> mode := OCamlOutput),
		"Generate OCaml code");

	("-prefix", Arg.String (fun n -> prefix := n),
		" <p> - Prefix generated module names with <p>");

  ("-bytes", Arg.String (fun n -> bytes := n),
		" <module> - Name of bytes module (must provide [l]bytes, pinverse_t, etc)");

  ("-add_fst", Arg.String (fun n -> headers := (let (u,v) = !headers in (n::u, v))),
		" <h> - Add <h> to the preamble of implementation files");

  ("-add_fsti", Arg.String (fun n -> headers := (let (u,v) = !headers in (u, n::v))),
    " <h> - Add <h> to the preamble of interface files");

  ("-odir", Arg.String (fun n -> odir := n),
    " <path> - Write generated modules to <path>");

] (fun s -> (ifile := s :: !ifile)) (sprintf "QuackyDucky %s\n%s"
	ver "Generates verified parsers and their specification from RFC");
	List.iter rfc_load !ifile
