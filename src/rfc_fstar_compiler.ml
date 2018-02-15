open Printf
open Rfc_ast

let pre = ref ""
let w = Printf.fprintf

(*
let qd_anon_prefix = "QD_ANONYMOUS_"
let qd_anon_counter = ref 0
let qd_bad_names = (Str.regexp ".*\(private_use\)\|\(obsolete\).*")

let rec pad = (fun n -> String.make (n*1) '\t')

and get_short_type x = (match x with
	| "uint8" -> ("u8", 1)
	| "uint16" -> ("u16", 2)
	| "uint32" -> ("u32", 4)
	| _ -> (x, 1))

and get_type x = (match x with
	| "uint8" -> ("UInt8.t", 1)
	| "uint16" -> ("UInt16.t", 2)
	| "uint32" -> ("UInt32.t", 4)
	| _ -> (x, 1))

and get_byte_length l p =
	let x = (float_of_int p) -. (float_of_int l) in
	int_of_float (ceil (x /. 255. /. 255.))

and get_literal_byte_length l =
	let pow = Str.search_forward l 0 in
	(match pow with
		| Not_found -> l
		| _ -> (sprintf "pow%s %s" ) (Str.string_before l pow) (Str.string_after l pow))

and rfc_generate_fstar prefix odir (p:Rfc_ast.prog) =
	fst_module_name := module_name;
	let print ac g = sprintf "%s\n\n%s" ac (match g with
		| Enum(ef, t) ->
			let n = String.uncapitalize t in
			sprintf "%s\n\n%s\n\n%s" (enum_type n ef) (enum_bytes n ef) (enum_parse n ef)
		| Struct(t, qual, sf) ->
			let n = String.uncapitalize t in
			let st = struct_type n sf in
			(sprintf "%s\n\n%s\n\n%s"
				(fst st)
				(* (struct_bytes n sf (snd st)) *)
				(struct_parse n sf (snd st))
				(struct_validate n sf (snd st))
			)
		| SelectStruct(e, m, l) ->
			let n = String.uncapitalize e in
			(sprintf "%s\n\n"
				(select_struct_type n l)
			)
		) in
		List.fold_left print
		(sprintf "module FStar.%s\n\n%s" !fst_module_name !fst_libs) p

and enum_type n (ef:Rfc_ast.enum_fields_t list) =
	let print ac f = sprintf "%s%s%s" ac (pad 1) (match f with
		| EnumFieldSimple(e, w) ->
			sprintf "| %s\n" (String.uppercase e)
		| EnumFieldAnonymous(l) -> ""
		| EnumFieldRange(e, l, m) ->
			(match (Str.string_match qd_bad_names e 0) with
				| true  -> sprintf ""
				| false -> sprintf "Incomplete:EnumFieldRange\n")) in
	List.fold_left print (sprintf "type %s =\n" n) ef

and enum_bytes n (ef:Rfc_ast.enum_fields_t list) =
	let tl = ref 0 in
	let ls = ref "" in
	let print ac f = sprintf "%s%s%s" ac (pad 1) (match f with
		| EnumFieldSimple(e, l) ->
			tl := !tl + (int_of_float (ceil ((float_of_int l) /. 255.)));
			sprintf "| %s ->%s %duy;\n" (String.uppercase e) !ls l
		| EnumFieldRange(e, l, m) ->
			(match (Str.string_match qd_bad_names e 0) with
				| true  -> sprintf ""
				| false -> sprintf "Incomplete:EnumFieldRange\n")
		| EnumFieldAnonymous(l) ->
			tl := !tl + (int_of_float (ceil ((float_of_int l) /. 255.)));
			(* ls := (match l with
				| 255 -> "le_uint8_serializer"
				| 65535 -> "le_uint16_serializer"
				| _ -> failwith "Enum length must be either 255 or 65535\n"); *)
			"") in
	(List.fold_left print "" ef);
	(sprintf "%s\n%s"
		(List.fold_left print
			(sprintf "let %s_as_enum : enum %s UInt8.t = [\n" n n) ef)
		(sprintf "]\nassume SizeOf%s: sizeof %s = %d"
			(String.capitalize n) n !tl))

and enum_parse n (ef:Rfc_ast.enum_fields_t list) =
	let print ac f = sprintf "%s%s%s" ac (pad 1) (match f with
		| EnumFieldSimple(e, l) ->
			sprintf "| (%dz) -> Correct %s\n" l (String.uppercase e)
		| EnumFieldAnonymous(l) ->
			qd_anon_counter := !qd_anon_counter + 1;
			sprintf "| (%dz) -> Correct %s%d\n" l qd_anon_prefix !qd_anon_counter
		| EnumFieldRange(e, l, m) ->
			(match (Str.string_match qd_bad_names e 0) with
				| true  -> sprintf ""
				| false -> sprintf "Incomplete:EnumFieldRange")) in
	(List.fold_left print "" ef);
	(List.fold_left print (sprintf "let parse_%s : parser %s_bytes\n" n n) ef)

and struct_type n (sf:Rfc_ast.struct_fields_t list) =
	let un = String.uncapitalize n in
	let bn = String.capitalize n in
	let sz = ref 0 in
	let print ac f = sprintf "%s\n%s%s" ac (pad 1) (match f with
		| StructFieldSimple(v, dv) -> (match v with
			| VectorSimple(t, y) ->
				let gt = get_type t in
				sz := !sz + (snd gt);
				(sprintf "%s: %s;" y (fst gt))
			| VectorSize(t, y, l) ->
				let gt = get_type t in
				sz := !sz + l;
				(sprintf "%s: buff %s %d;" y (fst gt) l)
			| VectorSymbolic(t, y, l) ->
				sprintf "Incomplete:VectorSymbolic"
			| VectorRange(t, y, (l, p)) ->
				let fl = float_of_int l in
				let fp = float_of_int p in
				let bl = get_byte_length l p in
				sz := !sz + bl;
				(sprintf "%s: bytes32 { let l = Seq.length identity in %d <= l /\\ l <= %d };" y l p))
		| StructFieldSelect(e, se, t) ->
			sprintf "%s" "SelectFields")
	in ((sprintf "%s" (sprintf "%s\n}\n" (List.fold_left print (sprintf "type %s = {" un) sf))), !sz)

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
	let ce = ref "" in
	let cl = ref "0" in
	let cs = ref "" in
	let print ac f = sprintf "%s\n%s%s" ac (pad 2) (match f with
		| StructFieldSimple(v, dv) -> (match v with
			| VectorSimple(t, y) ->
				let gt = get_type t in
				let ol = !ul in
				ul := !ul + (snd gt);
				cc := !cc + 1;
				cr := (sprintf "parse_%s" (fst (get_short_type t)));
				ce := (sprintf "%s\n%s%s = %s;" !ce (pad 1) y y);
				cs := (sprintf "%s%s, " !cs y);
				cl := (sprintf "%s+%dul" !cl (snd gt));
				(sprintf "%s%s\n%s%s"
					(pad 0) (sprintf "%s" !cr)
          (pad 2) (sprintf "`parse_nondep_pair`"))
			| VectorSize(t, y, l) ->
				let gt = get_type t in
				let ol = !ul in
				ul := !ul + l;
				cc := !cc + 1;
				ce := (sprintf "%s\n%s%s = %s;" !ce (pad 1) y y);
				cr := (sprintf "%s\n%s%s = %s;" !cr (pad 4) y y);
				cs := (sprintf "%s%s, " !cs y);
				cl := (sprintf "%s+%dul" !cl l);
				(sprintf "%s\n%s%s\n%s%s"
					(sprintf "let c%d = sub bytes %dul %dul in" !cc ol !ul)
					(pad 2) (sprintf "let c%d = cast %s c%d in" !cc (fst gt) !cc)
					(pad 2) (sprintf "let c%d = read c%d %dul in" !cc !cc ol))
			| VectorSymbolic(t, y, l) ->
				sprintf "Incomplete:VectorSymbolic"
			| VectorRange(t, y, (l, p)) ->
				cc := !cc + 1;
				ce := (sprintf "%s\n%s%s = %s;" !ce (pad 1) y y);
				cr := (sprintf "%s\n%s%s = %s;" !cr (pad 4) y y);
				cs := (sprintf "%s%s, " !cs y);
				(sprintf "%s\n%s%s"
					(sprintf "(parse_opaque_vlbytes %d %d)" l p)
					(pad 2) (sprintf "`parse_nondep_pair`")))
		| StructFieldSelect(e, se, t) ->
			sprintf "%s" "SelectFields")
	in (List.fold_left print "" sf); (ul := 0; cc := 0); (sprintf "%s\n%s"
		(List.fold_left print (sprintf "%s"
			(sprintf "let parse_%s: parser (%s) = (" n n)) sf)
			(sprintf ") `parse_synth`\n%s%s\n\n"
				(pad 0) (sprintf "(fun (%s) -> {%s\n})"
					(Str.string_before !cs ((String.length !cs) - 2))
					!ce
				)
			)
		)

and struct_validate n (sf:Rfc_ast.struct_fields_t list) sz =
	let ul = ref 0 in
	let cc = ref 0 in
	let cr = ref "" in
	let ce = ref "" in
	let cl = ref "0" in
	let cs = ref "" in
	let print ac f = sprintf "%s\n%s%s" ac (pad 2) (match f with
		| StructFieldSimple(v, dv) -> (match v with
			| VectorSimple(t, y) ->
				let gt = get_type t in
				let ol = !ul in
				ul := !ul + (snd gt);
				cc := !cc + 1;
				cr := (sprintf "validate_%s" (fst (get_short_type t)));
				ce := (sprintf "%s\n%s%s = %s;" !ce (pad 1) y y);
				cs := (sprintf "%s%s, " !cs y);
				cl := (sprintf "%s+%dul" !cl (snd gt));
				(sprintf "%s%s\n%s%s"
					(pad 0) (sprintf "%s" !cr)
          (pad 2) (sprintf "`validate_nondep_pair`"))
			| VectorSize(t, y, l) ->
				let gt = get_type t in
				let ol = !ul in
				ul := !ul + l;
				cc := !cc + 1;
				ce := (sprintf "%s\n%s%s = %s;" !ce (pad 1) y y);
				cr := (sprintf "%s\n%s%s = %s;" !cr (pad 4) y y);
				cs := (sprintf "%s%s, " !cs y);
				cl := (sprintf "%s+%dul" !cl l);
				(sprintf "%s\n%s%s\n%s%s"
					(sprintf "let c%d = sub bytes %dul %dul in" !cc ol !ul)
					(pad 2) (sprintf "let c%d = cast %s c%d in" !cc (fst gt) !cc)
					(pad 2) (sprintf "let c%d = read c%d %dul in" !cc !cc ol))
			| VectorSymbolic(t, y, l) ->
				sprintf "Incomplete:VectorSymbolic"
			| VectorRange(t, y, (l, p)) ->
				cc := !cc + 1;
				ce := (sprintf "%s\n%s%s = %s;" !ce (pad 1) y y);
				cr := (sprintf "%s\n%s%s = %s;" !cr (pad 4) y y);
				cs := (sprintf "%s%s, " !cs y);
				(sprintf "%s\n%s%s"
					(sprintf "(validate_opaque_vlbytes %d %d)" l p)
					(pad 2) (sprintf "`validate_nondep_pair`")))
		| StructFieldSelect(e, se, t) ->
			sprintf "%s" "SelectFields")
	in (List.fold_left print "" sf); (ul := 0; cc := 0); (sprintf "%s\n%s"
		(List.fold_left print (sprintf "%s"
			(sprintf "let validate_%s: stateful_validator (parse_%s) = (" n n)) sf)
			(sprintf ") `validate_synth`\n%s%s\n\n"
				(pad 0) (sprintf "(fun (%s) -> {%s\n})"
					(Str.string_before !cs ((String.length !cs) - 2))
					!ce
				)
			)
		)

and select_struct_type n (sf:(Rfc_ast.type_t * Rfc_ast.struct_fields_t list) list) =
  let print ac (c, q) = (sprintf "%s%s| %s:\n%s\n" ac (pad 0) (String.capitalize c) (
		List.fold_left (fun bc sft -> (sprintf "%s%s" bc (match sft with
			| StructFieldSimple(_) -> (sprintf "%s%s" (pad 1) "StructFieldSimple")
			| StructFieldSelect(tt, sftl, ttt) -> (sprintf "%s%s" (pad 1) "StructFieldSelect")))
		) "" q
	)) in
	(sprintf "!SELECT!%s\n"
		(List.fold_left print (sprintf "type %s\n" n) sf)
	)

*)

let tname (p:gemstone_t) =
  let aux = function
		| Enum (_, n) -> n
		| Struct (n, _, _) -> n
		| SelectStruct(n, _, _) -> n
	in String.uncapitalize (aux p)

let abs (n:type_t) =
  let n = String.uncapitalize n in
	!pre ^ n ^ "." ^ n

let compile_enum o n (fl: enum_fields_t list) =
  let repr_t, int_z, parse_t, blen =
	  let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
		        with _ -> failwith ("Enum "^n^" is missing a representation hint") in
	  match m with
		| EnumFieldAnonymous 255 -> "UInt8.t", "z", "u8", 1
		| EnumFieldAnonymous 65535 -> "UInt16.t", "us", "u16", 2
		| EnumFieldAnonymous 4294967295 -> "UInt32.t", "ul", "u32", 4
		| _ -> failwith ("Cannot represent enum type "^n^" (only u8, u16, u32 supported)")
	in
	let rec collect_valid_repr int_z acc = function
	  | [] -> if acc = "" then "True" else acc
		| (EnumFieldAnonymous _) :: t -> collect_valid_repr int_z acc t
		| (EnumFieldSimple (_, i)) :: t ->
		  let acc' =
			  (if acc = "" then acc else acc^" /\\ ")^
			  "v <> " ^ (string_of_int i) ^ int_z in
		  collect_valid_repr int_z acc' t
		| (EnumFieldRange (_, i, j)) :: t ->
		  let acc' = acc in (* For now we treat enum ranges as unknown
			  (if acc = "" then acc else acc^" /\\ ")^
			  "(v < " ^ (string_of_int i) ^ int_z ^
				" \\/ v > " ^ (string_of_int j) ^ int_z ^ ")" in *)
		  collect_valid_repr int_z acc' t
		in
	w o "type %s' =\n" n;
	List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w o "  | %s\n" (String.capitalize x)
		| _ -> ()) fl;
	w o "  | Unknown_%s of (v:%s{%s})\n\n" n repr_t (collect_valid_repr int_z "" fl);
  w o "type %s = v:%s'{~(Unknown_%s? v)}\n\n" n n n;
	w o "inline_for_extraction let %s_enum : LP.enum %s %s =\n" n n repr_t;
	w o "  [@inline_let] let e = [\n";
	List.iter (function
	  | EnumFieldSimple (x, i) ->
		  w o "    %s, %d%s;\n" (String.capitalize x) i int_z
		| _ -> ()) fl;
	w o "  ] in\n";
	w o "  [@inline_let] let no_dups =\n";
	w o "    assert_norm (L.noRepeats (L.map fst e));\n";
	w o "    assert_norm (L.noRepeats (L.map snd e))\n";
	w o "  in e\n\n";
	w o "inline_for_extraction let synth_%s' (x:LP.maybe_enum_key %s_enum) : Tot %s' = \n" n n n;
	w o "  match x with\n";
	w o "  | LP.Known k -> k\n";
	w o "  | LP.Unknown y ->\n";
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd %s_enum)) in\n" n;
  w o "    Unknown_%s v\n\n" n;
	w o "let lemma_synth_%s'_inj () : Lemma\n" n;
	w o "  (forall (x1 x2: LP.maybe_enum_key %s_enum).\n" n;
  w o "    synth_%s' x1 == synth_%s' x2 ==> x1 == x2) = ()\n\n" n n;
	w o "inline_for_extraction let synth_%s'_inv (x:%s') : Tot (LP.maybe_enum_key %s_enum) = \n" n n n;
	w o "  match x with\n";
	w o "  | Unknown_%s y ->\n" n;
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd %s_enum)) in\n" n;
	w o "    LP.Unknown v\n";
	w o "  | x ->\n";
	w o "    [@inline_let] let x1 : protocolVersion = x in\n";
	w o "    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst %s_enum))\n" n;
	w o "    LP.Known (x1 <: LP.enum_key %s_enum)\n\n" n;
	w o "let lemma_synth_%s'_inv () : Lemma\n" n;
  w o "  (forall (x: LP.maybe_enum_key %s_enum). synth_%s'_inv (synth_%s' x) == x) = ()\n\n" n n n;
	w o "let parse_maybe_%s_key : LP.parser _ (LP.maybe_enum_key %s_enum) =\n" n n;
  w o "  LP.parse_maybe_enum_key LP.parse_%s %s_enum\n\n" parse_t n;
	w o "let serialize_maybe_%s_key : LP.serializer parse_maybe_%s_key =\n" n n;
  w o "  LP.serialize_maybe_enum_key LP.parse_%s LP.serialize_%s %s_enum\n\n" parse_t parse_t n;
	w o "let parse_%s' : LP.parser _ %s' =\n" n n;
	w o "  lemma_synth_%s'_inj ();\n" n;
  w o "  parse_maybe_%s_key `LP.parse_synth` synth_%s'\n\n" n n;
  w o "let serialize_%s' : LP.serializer parse_%s' =\n" n n;
	w o "  lemma_synth_%s'_inj ();\n  lemma_synth_%s'_inv ();\n" n n;
	w o "  LP.serialize_synth _ synth_%s' serialize_maybe_%s_key synth_%s'_inv ()\n\n" n n n;
	w o "inline_for_extraction let parse32_maybe_%s_key : LP.parser32 parse_maybe_%s_key =\n" n n;
  w o "  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_%s %s_enum parse_maybe_%s_key ())\n\n" parse_t n n;
	w o "inline_for_extraction let parse32_%s' : LP.parser32 parse_%s' =\n" n n;
	w o "  lemma_synth_%s'_inj ();\n" n;
  w o "  LP.parse32_synth _ synth_%s' (fun x->synth_%s' x) parse32_maybe_%s_key ()\n\n" n n n;
	w o "inline_for_extraction let serialize32_maybe_%s_key : LP.serializer32 serialize_maybe_%s_key =\n" n n;
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac\n";
	w o "    #_ #_ #_ #LP.parse_%s #LP.serialize_%s // FIXME(implicits for machine int parsers)\n" parse_t parse_t;
  w o "    LP.serialize32_%s %s_enum serialize_maybe_%s_key ())\n\n" parse_t n n;
  w o "inline_for_extraction let serialize32_%s' : LP.serializer32 serialize_%s' =\n" n n;
	w o "  lemma_synth_%s'_inj ();\n  lemma_synth_%s'_inv ();\n" n n;
  w o "  LP.serialize32_synth _ synth_%s' _ serialize32_maybe_%s_key synth_%s'_inv (fun x->synth_%s'_inv x) ()\n\n" n n n n;
	w o "(****** TLS specific, probably hand written *******)\n\n(*\n";
  w o "inline_for_extraction let %s_bytes (x:%s') : Tot (lbytes %d) =\n" n n blen;
  w o "  serialize32_%s' x <: LP.bytes32\n\n" n;
	w o "inline_for_extraction let parse_%s : pinverse_t %s_bytes =\n" n n;
  w o "  fun x -> LP.parse32_total parse32_%s' v;\n" n;
  w o "    let (Some (v, _)) = parse32_%s' x in Correct v\n*)\n" n;
	()

let compile o (p:gemstone_t) =
  let n = tname p in
  w o "module %s%s\n\n" !pre n;
	w o "module LP = LowParse.SLow\n";
	w o "module L = FStar.List.Tot\n\n";
	w o "#reset-options \"--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2\"\n\n";
	match p with
	| Enum(fl, _) -> compile_enum o n fl
	| _ -> ()

let rfc_generate_fstar prefix odir (p:Rfc_ast.prog) =
  pre := prefix;
  let aux (p:gemstone_t) =
	  let n = tname p in
		let fn = sprintf "%s/%s%s.fst" odir prefix n in
	  printf "Writing parsers for type <%s> to <%s>...\n" n fn;
		let o = try open_out fn with _ -> failwith "Failed to create output file" in
		compile o p
	in List.iter aux p
