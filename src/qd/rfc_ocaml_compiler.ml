open Printf
open Rfc_ast

let fst_module_name = ref ""
let fst_libs = ref (sprintf
	"%s\n%s\n%s\n%s\n%s\n%s"
	"open FStar.Heap"
	"open FStar.HyperHeap"
	"open FStar.Seq"
	"open FStar.UInt8"
	"open FStar.ImmBuffer"
	"open FStar.Format"
)

let qd_anon_prefix = "QD_ANONYMOUS_"
let qd_anon_counter = ref 0
let qd_bad_names = Re.Posix.compile_pat ".*\(private_use\)\|\(obsolete\).*"

let rec pad = (fun n -> String.make (n*1) '\t')

and get_type x = (match x with
	| "uint8" -> ("u8", 1)
	| "uint16" -> ("u16", 2)
	| "uint32" -> ("u32", 4)
	| _ -> (x, 1))

and get_byte_length l p =
	let x = (float_of_int p) -. (float_of_int l) in
	int_of_float (ceil (x /. 255. /. 255.))

and rfc_generate_ocaml module_name (p:Rfc_ast.prog) =
	fst_module_name := module_name;
	let print ac g = sprintf "%s\n\n%s" ac (match g with
		| Enum(ef, t, _) ->
			let n = String.uncapitalize t in
			sprintf "%s\n\n%s\n\n%s" (enum_type n ef) (enum_bytes n ef) (enum_parse n ef)
		| Struct(t, qual, sf) ->
			let n = String.uncapitalize t in
			let st = struct_type n sf in
			(sprintf "%s\n\n%s\n\n%s"
				(fst st)
				(struct_bytes n sf (snd st))
				(struct_parse n sf (snd st))
			)
		| SelectStruct(e, m, l) ->
			sprintf "Incomplete:SelectStruct") in
		List.fold_left print
		(sprintf "module FStar.%s\n\n%s" !fst_module_name !fst_libs) p

and enum_type n (ef:Rfc_ast.enum_fields_t list) =
	let print ac f = sprintf "%s%s%s" ac (pad 1) (match f with
		| EnumFieldSimple(e, w) ->
			sprintf "| %s\n" (String.uppercase e)
		| EnumFieldAnonymous(l) -> ""
		| EnumFieldRange(e, l, m) ->
			(match (Re.execp qd_bad_names e) with
				| true  -> sprintf ""
				| false -> sprintf "Incomplete:EnumFieldRange\n")) in
	List.fold_left print (sprintf "type %s =\n" n) ef

and enum_bytes n (ef:Rfc_ast.enum_fields_t list) =
	let tl = ref 0 in
	let ls = ref "" in
	let print ac f = sprintf "%s%s%s" ac (pad 1) (match f with
		| EnumFieldSimple(e, l) ->
			tl := !tl + (int_of_float (ceil ((float_of_int l) /. 255.)));
			sprintf "| %s -> %s (uint_to_t %dul)\n" (String.uppercase e) !ls l
		| EnumFieldRange(e, l, m) ->
			(match (Re.execp qd_bad_names e) with
				| true  -> sprintf ""
				| false -> sprintf "Incomplete:EnumFieldRange\n")
		| EnumFieldAnonymous(l) ->
			tl := !tl + (int_of_float (ceil ((float_of_int l) /. 255.)));
			ls := (match l with
				| 255 -> "le_uint8_serializer"
				| 65535 -> "le_uint16_serializer"
				| _ -> failwith "Enum length must be either 255 or 65535\n");
			"") in
	(List.fold_left print "" ef);
	(sprintf "%s\n%s"
		(List.fold_left print
			(sprintf "let %s_bytes : serializer %s = function\n" n n) ef)
		(sprintf "\nassume SizeOf%s: sizeof %s = %d"
			(String.capitalize n) n !tl))

and enum_parse n (ef:Rfc_ast.enum_fields_t list) =
	let print ac f = sprintf "%s%s%s" ac (pad 1) (match f with
		| EnumFieldSimple(e, l) ->
			sprintf "| (%dz) -> Correct %s\n" l (String.uppercase e)
		| EnumFieldAnonymous(l) ->
			qd_anon_counter := !qd_anon_counter + 1;
			sprintf "| (%dz) -> Correct %s%d\n" l qd_anon_prefix !qd_anon_counter
		| EnumFieldRange(e, l, m) ->
			(match (Re.execp qd_bad_names e) with
				| true  -> sprintf ""
				| false -> sprintf "Incomplete:EnumFieldRange")) in
	(List.fold_left print "" ef);
	(List.fold_left print (sprintf "let parse_%s : parser %s_bytes\n" n n) ef)

and struct_type n (sf:Rfc_ast.struct_fields_t list) =
	let un = String.uncapitalize n in
	let bn = String.capitalize n in
	let tt = ref (sprintf "assume %sHasSize:\n\thasSize %s /\\ sizeof %s = 0" bn un un) in
	let sz = ref 0 in
	let print ac f = sprintf "%s\n%s%s" ac (pad 1) (match f with
		| StructFieldSimple(v, dv) -> (match v with
			| VectorSimple(t, y) ->
				let gt = get_type t in
				sz := !sz + (snd gt);
				tt := (sprintf "%s + sizeof (%s)" !tt (fst gt));
				(sprintf "%s: %s;" y (fst gt))
			| VectorSize(t, y, l) ->
				let gt = get_type t in
				sz := !sz + l;
				tt := (sprintf "%s + sizeof (%s %d)" !tt (fst gt) l);
				(sprintf "%s: buff %s %d;" y (fst gt) l)
			| VectorSymbolic(t, y, l) ->
				sprintf "Incomplete:VectorSymbolic"
			| VectorRange(t, y, (l, p)) ->
				let fl = float_of_int l in
				let fp = float_of_int p in
				let bl = get_byte_length l p in
				sz := !sz + bl;
				tt := (sprintf "%s + sizeof (vlbytes %d)" !tt bl);
				(sprintf "%s: vlbytes %d;" y (get_byte_length l p)))
		| StructFieldSelect(e, se, t) ->
			sprintf "%s" "SelectFields")
	in ((sprintf "%s\n%s"
		(sprintf "%s\n}\n" (List.fold_left print (sprintf "type %s = {" un) sf))
		!tt), !sz)

and struct_bytes n (sf:Rfc_ast.struct_fields_t list) sz =
	let vlc1 = ref "" in
	let vlc2 = ref "" in
	let vlcadd tt = (match !vlc1 with
		| "" ->
			vlc1 := (sprintf "%s_l" tt);
			vlc2 := (sprintf "%s_b" tt)
		| _  ->
			vlc1 := (sprintf "%s +^ %s_l" !vlc1 tt);
			vlc2 := (sprintf "%s @| %s_b" !vlc2 tt)) in
	let print ac f = sprintf "%s\n%s%s" ac (pad 1) (match f with
		| StructFieldSimple(v, dv) -> (match v with
			| VectorSimple(t, y) ->
				let tt = String.uncapitalize t in
				let gt = (get_type t) in
				vlcadd y;
				(sprintf "%s\n%s%s"
					(sprintf "let %s_b = %s_bytes %s.%s in" y tt n y)
					(pad 1)
					(sprintf "let %s_l = sizeof %s in" y (fst gt)))
			| VectorSize(t, y, l) ->
				vlcadd y;
				sprintf ""
			| VectorSymbolic(t, y, l) ->
				sprintf "Incomplete:VectorSymbolic"
			| VectorRange(t, y, (l, p)) ->
				vlcadd y;
				(sprintf "let (%s_l, %s_b) = %s.%s in" y y n y))
		| StructFieldSelect(e, se, t) ->
			sprintf "%s" "SelectFields")
	in (List.fold_left print "" sf);
	(sprintf "%s\n%s%s"
		(List.fold_left print (sprintf "let %s_bytes (%s:%s) : lserializer %s = " n n n n) sf)
		(pad 1)
		(sprintf "vlcreate (%s) (%s)" !vlc1 !vlc2))

and struct_parse n (sf:Rfc_ast.struct_fields_t list) sz =
	let ul = ref 0 in
	let cc = ref 0 in
	let cr = ref "" in
	let cl = ref "0" in
	let print ac f = sprintf "%s\n%s%s" ac (pad 2) (match f with
		| StructFieldSimple(v, dv) -> (match v with
			| VectorSimple(t, y) ->
				let gt = get_type t in
				let ol = !ul in
				ul := !ul + (snd gt);
				cc := !cc + 1;
				cr := (sprintf "%s\n%s%s = c_%d;" !cr (pad 4) y !cc);
				cl := (sprintf "%s+%dul" !cl (snd gt));
				(sprintf "%s\n%s%s\n%s%s"
					(sprintf "let c%d = sub bytes %dul %dul in" !cc ol !ul)
					(pad 2) (sprintf "let c%d = cast %s c%d in" !cc (fst gt) !cc)
					(pad 2) (sprintf "let c%d = read c%d %dul in" !cc !cc ol))
			| VectorSize(t, y, l) ->
				let gt = get_type t in
				let ol = !ul in
				ul := !ul + l;
				cc := !cc + 1;
				cr := (sprintf "%s\n%s%s = c_%d;" !cr (pad 4) y !cc);
				cl := (sprintf "%s+%dul" !cl l);
				(sprintf "%s\n%s%s\n%s%s"
					(sprintf "let c%d = sub bytes %dul %dul in" !cc ol !ul)
					(pad 2) (sprintf "let c%d = cast %s c%d in" !cc (fst gt) !cc)
					(pad 2) (sprintf "let c%d = read c%d %dul in" !cc !cc ol))
			| VectorSymbolic(t, y, l) ->
				sprintf "Incomplete:VectorSymbolic"
			| VectorRange(t, y, (l, p)) ->
				cc := !cc + 1;
				cr := (sprintf "%s\n%s%s = c_%d;" !cr (pad 4) y !cc);
				(sprintf "let c%d_bytes = lb_offset b %dul in" !cc !ul))
		| StructFieldSelect(e, se, t) ->
			sprintf "%s" "SelectFields")
	in (List.fold_left print "" sf); (ul := 0; cc := 0); (sprintf "%s\n%s\t)"
		(List.fold_left print (sprintf "%s\n%s%s\n%s%s\n%s%s\n%s%s"
			(sprintf "let vlparse_%s: lparser (vlserialize_%s) = fun b ->" n n)
			(pad 1) (sprintf "let len = lb_length b in")
			(pad 1) (sprintf "let bytes = lb_bytes b in")
			(pad 1) (sprintf "if len <^ %dul then Error \"Too short\"" sz)
			(pad 1) (sprintf "else (")) sf)
			(sprintf "%s%s\n%s%s\n%s%s\n"
			(pad 2) (sprintf "match vlparse %dul c%d_bytes with" !ul !cc)
			(pad 3) (sprintf "| Correct (blob,l) -> Correct ({%s}, %s + ^l)" !cr !cl)
			(pad 3) (sprintf "| Error z -> Error z")))
