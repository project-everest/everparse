open Printf

open Rfc_ast

let rec pad = (fun n -> String.make (n*2) ' ')

and attrs = List.fold_left (fun acc x -> sprintf "%s/*@%s*/ " acc x) ""

and rfc_pretty_print (prog:Rfc_ast.prog) =
	let print ac g = sprintf "%s\n%s" ac (match g with
	| Enum(attr, fl, n) ->
		sprintf "\n%senum {%s\n} %s;" (attrs attr) (print_enum_fields 1 fl) n
        | Abstract(attr, dn, min, max, n) ->
           sprintf "\n%sabstract %s = \"%s\" <%d..%d>;" (attrs attr) n dn min max
	| Struct(attr, fl, n) ->
		sprintf "\n%sstruct {%s\n} %s;" (attrs attr) (print_struct_fields 1 fl) n
  | Typedef(td) -> print_struct_fields 0 [td])
	in List.fold_left print "" prog

and print_vector = function
  | VectorNone -> ""
	| VectorFixed(n) -> sprintf "[%d]" n
	| VectorSymbolic(k) -> sprintf "[%s]" k
	| VectorRange(a,b,_) -> sprintf "<%d..%d>" a b
        | _ -> failwith "print_vector"

and print_enum_fields p (fl:enum_field_t list) =
	let print ac f = sprintf "%s\n%s%s" ac (pad p) (match f with
		| EnumFieldRange(e, a, b) ->
			sprintf "%s(%d..%d)" e a b
		| EnumFieldSimple(e, l) ->
			sprintf "%s(%d)," e l
		| EnumFieldAnonymous(l) ->
			sprintf "(%d)" l)
	in List.fold_left print "" fl

and print_struct_fields p (fl:struct_field_t list) =
	let print ac (attr, ty, n, v, def) =
    sprintf "%s\n%s%s%s %s%s%s;" ac (pad p) (attrs attr)
      (print_type p ty) n (print_vector v)
      (match def with None -> ""
      | Some [singl] -> sprintf " = %d" singl
      | Some il -> sprintf " = { %s }"
        (List.fold_left (fun acc i ->
          if acc = "" then sprintf "%d" i
          else sprintf "%s, %d" acc i) "" il))
	in List.fold_left print "" fl

and print_type p = function
	| TypeSimple t -> t
        | TypeIfeq (n, c, t, f) ->
           sprintf "if %s = %s %s else %s" n c t f
  | TypeSelect (n, cl, def) ->
    sprintf "select(%s) {\n%s%s%s}" n
    (print_select_fields (p+1) cl)
    (match def with None -> ""
    | Some dt -> sprintf "%sdefault: %s\n" (pad p) dt)
    (pad p)

and print_select_fields p (cl:(typ * typ) list) =
	let print ac (k,t) = sprintf "%s%scase %s: %s\n" ac (pad p) k t
	in List.fold_left print "" cl
