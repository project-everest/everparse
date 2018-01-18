open Printf

open Rfc_ast

let rec pad = (fun n -> String.make (n*1) '\t')

and rfc_pretty_print (prog:Rfc_ast.prog) = 
	let print ac g = sprintf "%s\n\n%s%s" ac (pad 0) (match g with
	| SelectStruct(t, sv, alts) ->
		let cases = print_switch 1 alts in
		sprintf "struct {\n\tselect(%s) {\n%s\t}\n} %s;\n" sv cases t
	| Enum(ef, t) ->
		sprintf "enum {%s\n} %s;" (print_enum_fields 1 ef) t
	| Struct(t, qual, sf) ->
				let qs = match qual with None -> "" | Some q -> q^" " in
		sprintf "%sstruct {%s\n} %s;" qs (print_struct_fields 1 sf) t)
	in List.fold_left print "" prog

and print_switch n = function
	| [] -> ""
	| (case, defs) :: t ->
		let casehdr = sprintf "%scase(%s):" (pad n) case in
		let defs = print_struct_fields (n+1) defs in
		casehdr ^ defs ^ "\n" ^ (print_switch n t)

and print_vector (v:Rfc_ast.vector_t) = (match v with
	| VectorSimple(t, n) ->
		sprintf "%s %s;" t n
	| VectorSymbolic(t, n, k) ->
		sprintf "%s %s[%s];" t n k
	| VectorSize(t, n, l) ->
		sprintf "%s %s[%d];" t n l
	| VectorRange(t, n, r) ->
		sprintf "%s %s <%d..%d>;" t n (fst r) (snd r))

and print_enum_fields p (ef:Rfc_ast.enum_fields_t list) = 
	let print ac f = sprintf "%s\n%s%s" ac (pad p) (match f with
		| EnumFieldRange(e, a, b) ->
			sprintf "%s(%d..%d)" e a b
		| EnumFieldSimple(e, l) ->
			sprintf "%s(%d)," e l
		| EnumFieldAnonymous(l) ->
			sprintf "(%d)" l)
	in List.fold_left print "" ef

and print_struct_fields p (sf:Rfc_ast.struct_fields_t list) =
	let print ac f = sprintf "%s\n%s%s" ac (pad p) (match f with
		| StructFieldSimple(v, dv) ->
			print_vector v
		| StructFieldSelect(t, sel, y) ->
			sprintf "select(%s) {%s\n\t} %s;" t (print_select_fields (p+1) sel) y)
	in List.fold_left print "" sf

and print_select_fields p (sf:Rfc_ast.select_fields_t list) =
	let print ac f = sprintf "%s\n%s%s" ac (pad p) (match f with
		| SelectField(e, t) ->
			sprintf "case %s: %s;" e t)
	in List.fold_left print "" sf
