open Globals
open Printf
open Rfc_ast

module SM = Map.Make (String)

type len_info = {
  mutable len_len: int;
  mutable min_len: int;
  mutable max_len: int;
  mutable min_count: int;
  mutable max_count: int;
  mutable vl : bool;
}

(* Recording the boundaries of variable length structures *)
let linfo : len_info SM.t ref = ref (SM.empty)

let w = fprintf

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

let log256 k =
  if k <= 255 then 1
  else if k <= 65535 then 2
  else if k <= 16777215 then 3
  else 4

let tname (p:gemstone_t) =
  let aux = function
		| Enum (_, n) -> n
		| Struct (n, _, _) -> n
		| SelectStruct(n, _, _) -> n
	in String.uncapitalize (aux p)

let get_leninfo (t:type_t) =
  try SM.find (String.uncapitalize t) !linfo
  with _ -> failwith ("Failed lookup for type "^t)

let li_add (s:string) (li:len_info) =
  printf "LINFO<%s>: vl=%s lenLen=%d minLen=%d maxLen=%d minCount=%d maxCount=%d\n" s (if li.vl then "yes" else "no") li.len_len li.min_len li.max_len li.min_count li.max_count;
  linfo := SM.add s li !linfo

let basic_type = function
  | "opaque" | "uint8" | "uint16" | "uint24" | "uint32" -> true
  | _ -> false

let sizeof (t:type_t) =
  match t with
  | "opaque"
  | "uint8"  -> { len_len = 0; min_len = 1; max_len = 1; min_count = 0; max_count = 0; vl = false; }
  | "uint16" -> { len_len = 0; min_len = 2; max_len = 2; min_count = 0; max_count = 0; vl = false; }
  | "uint24" -> { len_len = 0; min_len = 3; max_len = 3; min_count = 0; max_count = 0; vl = false; }
  | "uint32" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; }
  | s ->
    let li = get_leninfo t in
    {li with len_len = li.len_len} (* Copy *)

let add_field (tn:type_t) (v:vector_t) =
  match v with
  | VectorSimple (ty, n) ->
    let li = sizeof ty in
    li_add (tn^"@"^n) li; ty, li
  | VectorSize (ty, n, k) ->
    let li = sizeof ty in
    li.len_len <- 0;
    li.min_len <- li.min_len * k;
    li.max_len <- li.max_len * k;
    li.min_count <- k;
    li.max_count <- k;
    li_add (tn^"@"^n) li; ty, li
  | VectorSymbolic (ty, n, cst) ->
    let li = sizeof ty in
    li.vl <- true;
    li_add (tn^"@"^n) li; ty, li
  | VectorRange (ty, n, (low, high)) ->
    let li = sizeof ty in
    let h = log256 high in
    li.vl <- true;
    li.min_count <- low / (li.len_len + li.max_len);
    li.max_count <- high / (li.len_len + li.min_len);
    li.len_len <- h;
    li.min_len <- h + low;
    li.max_len <- h + high;
    li_add (tn^"@"^n) li; ty, li

let dep_len (p:gemstone_t) =
  let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; } in
  let tn = tname p in
  let depl = match p with
    | Enum (fl, n) ->
      let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
              with _ -> failwith ("Enum "^n^" is missing a representation hint") in
      (match m with
      | EnumFieldAnonymous 255 -> li.min_len <- 1; li.max_len <- 1
      | EnumFieldAnonymous 65535 -> li.min_len <- 2; li.max_len <- 2
      | EnumFieldAnonymous 4294967295 -> li.min_len <- 4; li.max_len <- 4);
      []
    | Struct (_, _, fl) ->
      let dep = List.map (function
        | StructFieldSimple (vec, _) ->
          let ty, lif = add_field tn vec in
          li.vl <- li.vl || lif.vl;
          li.min_len <- li.min_len + lif.min_len;
          li.max_len <- li.max_len + lif.max_len;
          [ty]
        | StructFieldSelect _ -> []) fl in
      List.flatten dep
    | SelectStruct _ -> []
    in
  li_add tn li;
  depl, li

let abs (n:type_t) =
  let n = String.uncapitalize n in
	!prefix ^ n ^ "." ^ n

let compile_type = function
  | "opaque"
  | "uint8" -> "U8.t"
  | "uint16" -> "U16.t"
  | "uint24" -> "U32.t"
  | "uint32" -> "U32.t"
  | t -> String.uncapitalize t

let pcombinator_name = function
  | "U8.t" -> "LP.parse_u8"
  | "U16.t" -> "LP.parse_u16"
  | "U32.t" -> "LP.parse_u32"
  | t -> t^"_parser"

let scombinator_name = function
  | "U8.t" -> "LP.serialize_u8"
  | "U16.t" -> "LP.serialize_u16"
  | "U32.t" -> "LP.serialize_u32"
  | t -> t^"_serializer"

let pcombinator32_name = function
  | "U8.t" -> "LP.parse32_u8"
  | "U16.t" -> "LP.parse32_u16"
  | "U32.t" -> "LP.parse32_u32"
  | t -> t^"_parser32"

let scombinator32_name = function
  | "U8.t" -> "LP.serialize32_u8"
  | "U16.t" -> "LP.serialize32_u16"
  | "U32.t" -> "LP.serialize32_u32"
  | t -> t^"_serializer32"

let size32_name = function
  | "U8.t" -> "LP.size32_constant LP.serialize_u8 1ul ()"
  | "U16.t" -> "LP.size32_constant LP.serialize_u16 2ul ()"
  | "U32.t" -> "LP.size32_constant LP.serialize_u32 4ul ()"
  | t -> t^"_size32"

let compile_struct o i n (fl: struct_fields_t list) =
  let li = get_leninfo n in
  let aux = function
    | VectorSimple (ty, fn) ->
      fn, compile_type ty
    | VectorSize ("opaque", fn, k) ->
      w i "type %s = lbytes %d\n\n" fn k;
      w o "let %s_parser = LP.parse_flbytes %d\n\n" fn k;
      w o "let %s_serializer = LP.serialize_flbytes %d\n\n" fn k;
      w o "let %s_bytesize (x:%s) = %d\n\n" fn fn k;
      w o "let %s_parser32 = LP.parse32_flbytes %d %dul\n\n" fn k k;
      w o "let %s_serializer32 = LP.serialize32_flbytes %d\n\n" fn k;
      w o "let %s_size32 = LP.size32_constant %s_serializer %dul\n\n" fn fn k;
      fn, fn
    | VectorSize (ty, fn, k) ->
      let ty0 = compile_type ty in
      let rec aux = function 1 -> ty0 | k -> sprintf "%s * %s" (aux (k-1)) ty0 in
      w i "type %s_vector%d = %s (* FStar.Vector.raw %s %dul *)\n" ty k (aux k) ty0 k;
      w o "let %s_vector%d_parser : LP.parser _ %s_vector%d =\n" ty k ty k;
      let c = pcombinator_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "%s\n  `LP.nondep_then` %s" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      w o "inline_for_extraction let %s_vector%d_parser32 : LP.parser32 %s_vector%d_parser =\n" ty k ty k;
      let c = pcombinator32_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "%s\n  `LP.parse32_nondep_then` %s" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      w o "inline_for_extraction let %s_vector%d_serializer : LP.serializer %s_vector%d_parser = admit()\n\n" ty k ty k;
      w o "inline_for_extraction let %s_vector%d_serializer32 : LP.serializer32 %s_vector%d_serializer = admit()\n\n" ty k ty k;
      w o "inline_for_extraction let %s_vector%d_size32 : LP.size32 %s_vector%d_serializer = admit()\n\n" ty k ty k;
      fn, sprintf "%s_vector%d" ty k (*aux k*)
    | VectorSymbolic (ty, fn, cst) ->
      let ty0 = compile_type ty in
      fn, sprintf "FStar.Vector.raw %s %s" ty0 cst
    | VectorRange ("opaque", fn, (low, high)) ->
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" fn low high;
      w o "let %s_parser = LP.parse_bounded_vlbytes %d %d\n\n" fn low high;
      w o "let %s_serializer = LP.serialize_bounded_vlbytes %d %d\n\n" fn low high;
      w o "let %s_bytesize (x:%s) : GTot nat = Seq.length (%s_serializer x)\n\n" fn fn fn;
      w o "let %s_parser32 = LP.parse32_bounded_vlbytes %d %dul %d %dul\n\n" fn low low high high;
      w o "let %s_serializer32 = LP.serialize32_bounded_vlbytes %d %d\n\n" fn low high;
      w o "let %s_size32 = LP.size32_bounded_vlbytes %d %d\n\n" fn low high;
      fn, fn
    | VectorRange (ty, fn, (low, high)) ->
      let li = get_leninfo (n^"@"^fn) in
      let ty0 = compile_type ty in
      if li.min_len = li.max_len then
        (fn, sprintf "l:list %s{%d <= L.length l /\\ L.length l <= %d}" ty0 li.min_count li.max_count)
      else
       begin
        (* refined field type with variable length constraint *)
        let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
        w i "val %s_bytesize: list %s -> GTot nat\n" fn ty0;
        w o "let %s_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s_serializer) x)\n\n" fn ty0;
        w i "inline_for_extraction val %s_bytesize32: x:list %s -> y:U32.t{\n" fn ty0;
        w i "  let s = %s_bytesize x in\n  if s > U32.v (LP.u32_max) then y == LP.u32_max else U32.v y == s}\n\n" fn;
        w o "let %s_bytesize32 x = LP.size32_list %s_size32 () x\n\n" fn ty0;
        w i "type %s = l:list %s{let x = %s_bytesize l in %d <= x /\\ x <= %d}\n\n" fn ty0 fn min max;

        (* vldata list parser *)
        (** TODO replace parse_bounded_vldata_strong with parse32_vlarray *)
        (*
        w o "let %s_parser : LP.parser _ %s =\n" fn fn;
        w o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" min max (pcombinator_name ty0) li.min_count li.max_count;
        w o "  LP.parse_vlarray %d %d %s %d %d ()\n\n" min max (scombinator_name ty0) li.min_count li.max_count;
        w o "let %s_serializer : LP.serializer %s_parser =\n" fn fn;
        w o "  LP.serialize_vlarray %d %d %s %d %d ()\n\n" min max (scombinator_name ty0) li.min_count li.max_count;
        w o "let %s_parser32 : LP.parser32 %s =\n" fn fn;
        w o "  LP.parse32_vlarray %d %dul %d %dul %s %s %d %d ()\n\n" min min max max (scombinator_name ty0) (pcombinator_name ty0) li.min_count li.max_count;
        *)

        w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d (LP.serialize_list _ %s_serializer)\n\n" fn min max ty0;
        w o "let %s'_parser : LP.parser _ %s' =\n" fn fn;
        w o "  LP.parse_bounded_vldata_strong %d %d (LP.serialize_list _ %s_serializer)\n\n" min max ty0;
        w o "let %s'_serializer : LP.serializer %s'_parser =\n" fn fn;
        w o "  LP.serialize_bounded_vldata_strong %d %d (LP.serialize_list _ %s_serializer)\n\n" min max ty0;
        w o "let %s'_parser32 : LP.parser32 %s'_parser =\n" fn fn;
        w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul (LP.serialize_list _ %s_serializer) (LP.parse32_list %s_parser32)\n\n" min min max max ty0 ty0;
        w o "let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" fn fn;
        w o "  LP.serialize32_bounded_vldata_strong %d %d (LP.partial_serialize32_list _ %s_serializer %s_serializer32 ())\n\n" min max ty0 ty0;
        w o "let %s'_size32 : LP.size32 %s'_serializer =\n" fn fn;
        w o "  LP.size32_bounded_vldata_strong %d %d (LP.size32_list %s_size32 ()) %dul\n\n" min max ty0 li.len_len;
        fn, fn^"'"
       end
    in
  let fields = List.map (function
    | StructFieldSimple (vec, _) -> aux vec
    | StructFieldSelect (n, _, _) -> Printf.printf "WARNING: ignored a select()\n"; n, "") fl
    in

  let fields = List.filter (fun (_, ty) -> ty <> "") fields in

  (* application type *)
  w i "type %s = {\n" n;
  List.iter (fun (fn, ty) ->
    let ty =
      if ty = "" then "" else
      (if Str.last_chars ty 1 = "'" then Str.first_chars ty (String.length ty - 1) else ty) in
    w i "\t%s: %s;\n" fn ty) fields;
  w i "}\n\n";

  (* Tuple type for nondep_then combination *)
  let tuple = List.fold_left (fun acc (_, ty) -> if acc="" then ty else sprintf "(%s * %s)" acc ty) "" fields in
  w o "type %s' = %s\n\n" n tuple;

  (* synthethizer for tuple type *)
  w o "inline_for_extraction let synth_%s (x: %s') : %s =\n" n n n;
  let tuple = List.fold_left (fun acc (fn, ty) -> if acc="" then fn else sprintf "(%s, %s)" acc fn) "" fields in
  w o "  let %s = x in\n  {\n" tuple;
  let tuple = List.fold_left (fun acc (fn, ty) -> sprintf "%s    %s = %s;\n" acc fn fn) "" fields in
  w o "%s  }\n\n" tuple;
  w o "inline_for_extraction let synth_%s_recip (x: %s) : %s' =\n" n n n;
  let tuple = List.fold_left (fun acc (fn, ty) -> if acc="" then "x."^fn else sprintf "(%s, x.%s)" acc fn) "" fields in
  w o "  %s\n\n" tuple;

  (* synthetizer injectivity and inversion lemmas *)
  w o "let synth_%s_injective ()\n  : Lemma (LP.synth_injective synth_%s) = ()\n\n" n n;
  w o "let synth_%s_inverse ()\n  : Lemma (LP.synth_inverse synth_%s synth_%s_recip) = ()\n\n" n n n;

  (* main parser combinator type *)
  w o "let %s'_parser : LP.parser _ %s' =\n" n n;
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator_name ty in
      if acc="" then c else sprintf "%s\n  `LP.nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;
  let li = get_leninfo n in

  w i "inline_for_extraction val %s_parser_kind_metadata : LP.parser_kind_metadata_t\n\n" n;
  w o "inline_for_extraction let %s'_parser_kind = LP.get_parser_kind %s'_parser\n\n" n n;
  w o "let %s_parser_kind_metadata = %s'_parser_kind.LP.parser_kind_metadata\n\n" n n;
  w i "inline_for_extraction let %s_parser_kind = LP.strong_parser_kind %d %d %s_parser_kind_metadata\n\n" n li.min_len li.max_len n;
  let li = get_leninfo n in

  w i "val %s_parser: LP.parser %s_parser_kind %s\n\n" n n n;
  w o "let %s_parser =\n  synth_%s_injective ();\n  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n n n;
  w o "  %s'_parser `LP.parse_synth` synth_%s\n\n" n n;

  (* main parser32 *)
  w i "inline_for_extraction val %s_parser32: LP.parser32 %s_parser\n\n" n n;
  w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator32_name ty in
      if acc="" then c else sprintf "%s\n  `LP.parse32_nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;
  w o "let %s_parser32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.parse32_synth _ synth_%s (fun x -> synth_%s x) %s'_parser32 ()\n\n" n n n;

  (* main serializer type *)
  w i "val %s_serializer: LP.serializer %s_parser\n\n" n n;
  w o "let %s'_serializer : LP.serializer %s'_parser =\n" n n;
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = scombinator_name ty in
      if acc="" then c else sprintf "LP.serialize_nondep_then _ (%s) ()\n  _ %s" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;
  w o "let %s_serializer =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize_synth _ synth_%s %s'_serializer synth_%s_recip ()\n\n" n n n;

  (* serialize32 *)
  w i "inline_for_extraction val %s_serializer32: LP.serializer32 %s_serializer\n\n" n n;
  w o "let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = scombinator32_name ty in
      if acc="" then c else sprintf "LP.serialize32_nondep_then (%s) ()\n  %s ()" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;

  w o "let %s_serializer32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize32_synth _ synth_%s _ %s'_serializer32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;

  (* size32 *)
  (* FIXME use   assert_norm (LP.size32_constant_precond LP.serialize_X Kul *)
  w o "let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = size32_name ty in
      if acc="" then c else sprintf "LP.size32_nondep_then (%s) ()\n  (%s)" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;

  w i "inline_for_extraction val %s_size32: LP.size32 %s_serializer\n\n" n n;
  w o "let %s_size32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.size32_synth _ synth_%s _ %s'_size32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;
  ()

let compile_enum o i n (fl: enum_fields_t list) =

  let repr_t, int_z, parse_t, blen =
	  let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
		        with _ -> failwith ("Enum "^n^" is missing a representation hint") in
	  match m with
		| EnumFieldAnonymous 255 -> "U8.t", "z", "u8", 1
		| EnumFieldAnonymous 65535 -> "U16.t", "us", "u16", 2
		| EnumFieldAnonymous 4294967295 -> "U32.t", "ul", "u32", 4
		| _ -> failwith ("Cannot represent enum type "^n^" (only u8, u16, u32 supported)")
	in

	let rec collect_valid_repr int_z acc = function
	  | [] -> if acc = "" then "True" else acc
		| (EnumFieldAnonymous _) :: t -> collect_valid_repr int_z acc t
		| (EnumFieldSimple (_, i)) :: t ->
		  let acc' =
			  if acc = "" then sprintf "v <> %d%s" i int_z
        else sprintf "%s /\\ v <> %d%s" acc i int_z in
		  collect_valid_repr int_z acc' t
		| (EnumFieldRange (_, i, j)) :: t ->
		  let acc' = acc in (* For now we treat enum ranges as unknown
			  (if acc = "" then acc else acc^" /\\ ")^
			  "(v < " ^ (string_of_int i) ^ int_z ^
				" \\/ v > " ^ (string_of_int j) ^ int_z ^ ")" in *)
		  collect_valid_repr int_z acc' t
		in

	w i "type %s' =\n" n;
	List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w i "  | %s\n" (String.capitalize x)
		| _ -> ()) fl;
	w i "  | Unknown_%s of (v:%s{%s})\n\n" n repr_t (collect_valid_repr int_z "" fl);
  w i "type %s = v:%s'{~(Unknown_%s? v)}\n\n" n n n;

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

  (* Synth *)
	w o "inline_for_extraction let synth_%s' (x:LP.maybe_enum_key %s_enum) : %s' = \n" n n n;
	w o "  match x with\n";
	w o "  | LP.Known k -> k\n";
	w o "  | LP.Unknown y ->\n";
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = LP.norm_spec (LP.list_mem v (LP.list_map snd %s_enum)) in\n" n;
  w o "    Unknown_%s v\n\n" n;
	w o "let lemma_synth_%s'_inj () : Lemma\n" n;
	w o "  (forall (x1 x2: LP.maybe_enum_key %s_enum).\n" n;
  w o "    synth_%s' x1 == synth_%s' x2 ==> x1 == x2) = ()\n\n" n n;
	w o "inline_for_extraction let synth_%s'_inv (x:%s') : LP.maybe_enum_key %s_enum = \n" n n n;
	w o "  match x with\n";
	w o "  | Unknown_%s y ->\n" n;
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = LP.norm_spec (LP.list_mem v (LP.list_map snd %s_enum)) in\n" n;
	w o "    LP.Unknown v\n";
	w o "  | x ->\n";
	w o "    [@inline_let] let x1 : protocolVersion = x in\n";
	w o "    [@inline_let] let _ = LP.norm_spec (LP.list_mem x1 (LP.list_map fst %s_enum)) in\n" n;
	w o "    LP.Known (x1 <: LP.enum_key %s_enum)\n\n" n;
	w o "let lemma_synth_%s'_inv () : Lemma\n" n;
  w o "  (forall (x: LP.maybe_enum_key %s_enum). synth_%s'_inv (synth_%s' x) == x) = ()\n\n" n n n;

  (* Parse *)
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

  (* Parse32 *)
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

  w i "inline_for_extraction val %s_parser_kind_metadata : LP.parser_kind_metadata_t\n" n;

  w i "inline_for_extraction let %s_parser_kind = LP.strong_parser_kind %d %d %s_parser_kind_metadata\n\n" n blen blen n;

  w i "inline_for_extraction val %s_parser: LP.parser %s_parser_kind %s\n" n n n;

  w o "let %s_bytes x = serialize32_%s' x <: LP.bytes32\n\n" n n;

  w i "inline_for_extraction val %s_parser32: LP.parser32 %s_parser\n\n" n n;

	w o "let parse_%s' x =\n" n;
  w o "  LP.parse32_total parse32_%s' v;\n" n;
  w o "  match parse32_%s' x with\n" n;
  w o "  | Some (v, _) -> %s v\n" !opt_some;
  w o "  | None -> %s\n\n" !opt_none;

  w i "inline_for_extraction val %s_serializer: LP.serializer %s_parser\n" n n;

  w o "let parse_%s x =\n" n;
  w o "  LP.parse32_total parse32_%s' v;\n" n;
  w o "  match parse32_%s' x with\n" n;
  w o "  | Some (v, _) -> if v = Unknown_%s then %s else %s v\n" n !opt_none !opt_some;
  w o "  | None -> %s\n\n" !opt_none;

  w i "inline_for_extraction val %s_serializer32: LP.serializer32 %s_serializer\n\n" n n;

  w i "inline_for_extraction val %s_size32: LP.size32 %s_serializer\n\n" n n;
  w o "let %s_size32 = LP.size32_constant LP.%s_serializer %dul ()\n\n" n n blen;
	()

let compile o i (p:gemstone_t) =
  let n = tname p in
  let (fst, fsti) = !headers in

  (* .fsti *)
  w i "module %s%s\n\n" !prefix n;
  w i "open %s\n" !bytes;

  let depl, li = dep_len p in
  let depl = List.filter (fun x -> not (basic_type x)) depl in
  let depl = List.map (fun s -> !prefix ^ (String.uncapitalize s)) depl in
  (List.iter (w i "open %s\n") depl);
  w i "\n";

  w i "module U8 = FStar.UInt8\n";
  w i "module U16 = FStar.UInt16\n";
  w i "module U32 = FStar.UInt32\n";
  w i "module LP = LowParse.SLow.Base\n";
  w i "module L = FStar.List.Tot\n";
  (List.iter (w i "%s\n") (List.rev fsti));
  w i "\n";

  (* .fst *)
  w o "module %s%s\n\n" !prefix n;

  w o "open %s\n" !bytes;
  (List.iter (w o "open %s\n") depl);
  w o "\n";

  w o "module U8 = FStar.UInt8\n";
  w o "module U16 = FStar.UInt16\n";
  w o "module U32 = FStar.UInt32\n";
	w o "module LP = LowParse.SLow\n";
	w o "module L = FStar.List.Tot\n";
  (List.iter (w o "%s\n") (List.rev fst));
  w o "\n";

	w o "#reset-options \"--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 3 --max_ifuel 3\"\n\n";
	match p with
	| Enum(fl, _) -> compile_enum o i n fl
  | Struct(_, _, fl) -> compile_struct o i n fl
	| _ -> ()

let rfc_generate_fstar (p:Rfc_ast.prog) =
  let aux (p:gemstone_t) =
	  let n = tname p in
		let fn = sprintf "%s/%s%s.fst" !odir !prefix n in
	  printf "Writing parsers for type <%s> to <%s>...\n" n fn;
		let o, i = try open_out fn, open_out (fn^"i")
               with _ -> failwith "Failed to create output file" in
		compile o i p;
    close_out o
	in List.iter aux p
