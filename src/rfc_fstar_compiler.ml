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

let log256 k =
  if k <= 255 then 1
  else if k <= 65535 then 2
  else if k <= 16777215 then 3
  else 4

let tname (p:gemstone_t) : string =
  let aux = function
		| Enum (_, _, n) -> n
		| Struct (_, _, n) -> n
    | Typedef (_, _, n, _, _) -> n
	in String.uncapitalize (aux p)

let get_leninfo (t:typ) =
  try SM.find (String.uncapitalize t) !linfo
  with _ -> failwith ("Failed lookup for type "^t)

(*
let li_add (s:string) (li:len_info) =
  printf "LINFO<%s>: vl=%s lenLen=%d minLen=%d maxLen=%d minCount=%d maxCount=%d\n" s (if li.vl then "yes" else "no") li.len_len li.min_len li.max_len li.min_count li.max_count;
  linfo := SM.add s li !linfo

let basic_type = function
  | "opaque" | "uint8" | "uint16" | "uint24" | "uint32" -> true
  | _ -> false

let sizeof (t:typ) =
  match t with
  | "opaque"
  | "uint8"  -> { len_len = 0; min_len = 1; max_len = 1; min_count = 0; max_count = 0; vl = false; }
  | "uint16" -> { len_len = 0; min_len = 2; max_len = 2; min_count = 0; max_count = 0; vl = false; }
  | "uint24" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; }
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
    (if li.len_len + li.max_len = 0 then failwith ("Can't compute count bound on "^ty));
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
    | Enum (fl, n, attr) ->
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

let rec compile_struct o i n (fl: struct_fields_t list) =
  let li = get_leninfo n in
  let aux = function
    | VectorSimple (ty, fn) ->
      fn, compile_type ty
    | VectorSize ("opaque", fn0, k) ->
      let fn = if fn0 = n then fn0^"_field" else fn0 in
      w i "type %s = lbytes %d\n\n" fn k;
      w o "noextract let %s_parser = LP.parse_flbytes %d\n\n" fn k;
      w o "noextract let %s_serializer = LP.serialize_flbytes %d\n\n" fn k;
      w o "noextract let %s_bytesize (x:%s) = %d\n\n" fn fn k;
      w o "inline_for_extraction let %s_parser32 = LP.parse32_flbytes %d %dul\n\n" fn k k;
      w o "inline_for_extraction let %s_serializer32 = LP.serialize32_flbytes %d\n\n" fn k;
      w o "inline_for_extraction let %s_size32 = LP.size32_constant %s_serializer %dul ()\n\n" fn fn k;
      fn0, fn
    | VectorSize (ty, fn, k) ->
      let ty0 = compile_type ty in
      let rec aux = function 1 -> ty0 | k -> sprintf "%s * %s" (aux (k-1)) ty0 in
      w i "type %s_vector%d = %s (* FStar.Vector.raw %s %dul *)\n" ty k (aux k) ty0 k;
      w o "noextract let %s_vector%d_parser : LP.parser _ %s_vector%d =\n" ty k ty k;
      let c = pcombinator_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "%s\n  `LP.nondep_then` %s" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      w o "inline_for_extraction let %s_vector%d_parser32 : LP.parser32 %s_vector%d_parser =\n" ty k ty k;
      let c = pcombinator32_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "%s\n  `LP.parse32_nondep_then` %s" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      w o "noextract let %s_vector%d_serializer : LP.serializer %s_vector%d_parser =\n" ty k ty k;
      let c = scombinator_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "LP.serialize_nondep_then _ (%s) ()\n  _ %s" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      w o "inline_for_extraction let %s_vector%d_serializer32 : LP.serializer32 %s_vector%d_serializer =\n" ty k ty k;
      let c = scombinator32_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "LP.serialize32_nondep_then (%s) ()\n  %s ()" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      w o "inline_for_extraction let %s_vector%d_size32 : LP.size32 %s_vector%d_serializer =\n" ty k ty k;
      let c = size32_name ty0 in
      let rec aux k = if k = 1 then c else sprintf "LP.size32_nondep_then (%s) ()\n  (%s)" (aux (k-1)) c in
      w o "  %s\n\n" (aux k);
      fn, sprintf "%s_vector%d" ty k (*aux k*)
    | VectorSymbolic (ty, fn, cst) ->
      let ty0 = compile_type ty in
      fn, sprintf "FStar.Vector.raw %s %s" ty0 cst
    | VectorRange ("opaque", fn0, (low, high)) ->
      let fn = if fn0 = n then fn0^"_field" else fn0 in
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" fn low high;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes %d %d\n\n" fn low high;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes %d %d\n\n" fn low high;
      w o "noextract let %s_bytesize (x:%s) : GTot nat = Seq.length (%s_serializer x)\n\n" fn fn fn;
      w o "inline_for_extraction let %s_parser32 = LP.parse32_bounded_vlbytes %d %dul %d %dul\n\n" fn low low high high;
      w o "inline_for_extraction let %s_serializer32 = LP.serialize32_bounded_vlbytes %d %d\n\n" fn low high;
      w o "inline_for_extraction let %s_size32 = LP.size32_bounded_vlbytes %d %d %dul\n\n" fn low high (log256 high);
      fn0, fn
    | VectorRange (ty, fn, (low, high)) ->
      let li = get_leninfo (n^"@"^fn) in
      let ty0 = compile_type ty in
      if li.min_len = li.max_len then
        (fn, sprintf "l:list %s{%d <= L.length l /\\ L.length l <= %d}" ty0 li.min_count li.max_count)
      else
       begin
        (* refined field type with variable length constraint *)
        let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
        w i "noextract val %s_bytesize: list %s -> GTot nat\n" fn ty0;
        w o "let %s_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s_serializer) x)\n\n" fn ty0;
        w i "inline_for_extraction val %s_bytesize32: x:list %s -> y:U32.t{\n" fn ty0;
        w i "  let s = %s_bytesize x in\n  if s > U32.v (LP.u32_max) then y == LP.u32_max else U32.v y == s}\n\n" fn;
        w o "let %s_bytesize32 x = LP.size32_list %s_size32 () x\n\n" fn ty0;
        w i "type %s = l:list %s{let x = %s_bytesize l in %d <= x /\\ x <= %d}\n\n" fn ty0 fn min max;

        (* vldata list parser *)
        (** TODO replace parse_bounded_vldata_strong with parse32_vlarray *)
        (* if li.max_len = li.min_len then
        w o "let %s_parser : LP.parser _ %s =\n" fn fn;
        w o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" min max (pcombinator_name ty0) li.min_count li.max_count;
        w o "  LP.parse_vlarray %d %d %s %d %d ()\n\n" min max (scombinator_name ty0) li.min_count li.max_count;
        w o "let %s_serializer : LP.serializer %s_parser =\n" fn fn;
        w o "  LP.serialize_vlarray %d %d %s %d %d ()\n\n" min max (scombinator_name ty0) li.min_count li.max_count;
        w o "let %s_parser32 : LP.parser32 %s =\n" fn fn;
        w o "  LP.parse32_vlarray %d %dul %d %dul %s %s %d %d ()\n\n" min min max max (scombinator_name ty0) (pcombinator_name ty0) li.min_count li.max_count;
        else *)

        w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d (LP.serialize_list _ %s_serializer)\n\n" fn min max ty0;
        w o "noextract let %s'_parser : LP.parser _ %s' =\n" fn fn;
        w o "  LP.parse_bounded_vldata_strong %d %d (LP.serialize_list _ %s_serializer)\n\n" min max ty0;
        w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" fn fn;
        w o "  LP.serialize_bounded_vldata_strong %d %d (LP.serialize_list _ %s_serializer)\n\n" min max ty0;
        w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" fn fn;
        w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul (LP.serialize_list _ %s_serializer) (LP.parse32_list %s_parser32)\n\n" min min max max ty0 ty0;
        w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" fn fn;
        w o "  LP.serialize32_bounded_vldata_strong %d %d (LP.partial_serialize32_list _ %s_serializer %s_serializer32 ())\n\n" min max ty0 ty0;
        w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" fn fn;
        w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
        w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
        w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";
        w o "  LP.size32_bounded_vldata_strong %d %d (LP.size32_list %s_size32 ()) %dul\n\n" min max ty0 li.len_len;
        fn, fn^"'"
       end
    in

  let fields = List.map (function
    | StructFieldSimple (vec, _) -> aux vec
    | StructFieldSelect (sel, fl, fn0) ->
      let fn = if n=fn0 then n^"_field" else fn0 in
      w i "type %s =\n" fn;
      List.iter (fun (SelectField (case, ty)) -> w i "  | %s of %s\n" (String.uppercase case) (compile_type ty)) fl;
      w i "\n";
      (fn0, fn)) fl
    in

  let fields = List.filter (fun (_, ty) -> ty <> "") fields in

  (* application type *)
  if fields = [] then
    w i "type %s = lbytes 0\n\n" n
  else
   begin
    w i "type %s = {\n" n;
    List.iter (fun (fn, ty) ->
      let ty =
        if ty = "" then "" else
        (if Str.last_chars ty 1 = "'" then Str.first_chars ty (String.length ty - 1) else ty) in
      w i "\t%s: %s;\n" fn ty) fields;
    w i "}\n\n"
   end;

  (* Tuple type for nondep_then combination *)
  let tuple = List.fold_left (fun acc (_, ty) -> if acc="" then ty else sprintf "(%s * %s)" acc ty) "" fields in
  let tuple = if fields = [] then "lbytes 0" else tuple in

  w o "type %s' = %s\n\n" n tuple;

  (* synthethizer for tuple type *)
  w o "inline_for_extraction let synth_%s (x: %s') : %s =\n" n n n;

  if fields = [] then
    w o "  x\n\n"
  else
   begin
    let tuple = List.fold_left (fun acc (fn, ty) -> if acc="" then fn else sprintf "(%s, %s)" acc fn) "" fields in
    w o "  let %s = x in\n  {\n" tuple;
    let tuple = List.fold_left (fun acc (fn, ty) -> sprintf "%s    %s = %s;\n" acc fn fn) "" fields in
    w o "%s  }\n\n" tuple;
    w o "inline_for_extraction let synth_%s_recip (x: %s) : %s' =\n" n n n;
    let tuple = List.fold_left (fun acc (fn, ty) -> if acc="" then "x."^fn else sprintf "(%s, x.%s)" acc fn) "" fields in
    w o "  %s\n\n" tuple
   end;

  (* synthetizer injectivity and inversion lemmas *)
  w o "let synth_%s_injective ()\n  : Lemma (LP.synth_injective synth_%s) = admit() // FIXME \n\n" n n;
  w o "let synth_%s_inverse ()\n  : Lemma (LP.synth_inverse synth_%s synth_%s_recip) =\n" n n n;
  w o "  assert_norm (LP.synth_inverse synth_%s synth_%s_recip)\n\n" n n;

  (* main parser combinator type *)
  w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
  if fields = [] then w o "  LP.parse_flbytes 0";
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator_name ty in
      if acc="" then c else sprintf "%s\n  `LP.nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;
  let li = get_leninfo n in

  w i "noextract val %s_parser_kind_metadata : LP.parser_kind_metadata_t\n\n" n;
  w o "noextract let %s'_parser_kind = LP.get_parser_kind %s'_parser\n\n" n n;
  w o "let %s_parser_kind_metadata = %s'_parser_kind.LP.parser_kind_metadata\n\n" n n;
  w i "noextract let %s_parser_kind = LP.strong_parser_kind %d %d %s_parser_kind_metadata\n\n" n li.min_len li.max_len n;
  let li = get_leninfo n in

  w i "noextract val %s_parser: LP.parser %s_parser_kind %s\n\n" n n n;
  w o "let %s_parser =\n  synth_%s_injective ();\n  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n n n;
  w o "  %s'_parser `LP.parse_synth` synth_%s\n\n" n n;

  (* main parser32 *)
  w i "inline_for_extraction val %s_parser32: LP.parser32 %s_parser\n\n" n n;
  w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
  if fields = [] then w o "  LP.parse32_flbytes 0 0ul";
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
  w i "noextract val %s_serializer: LP.serializer %s_parser\n\n" n n;
  w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
  if fields = [] then w o "  LP.serialize_flbytes 0";
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
  if fields = [] then w o "  LP.serialize32_flbytes 0";
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
  w o "let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";
  if fields = [] then w o "  LP.size32_constant %s'_serializer 0ul ()" n;
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

and compile_enum o i n (fl: enum_fields_t list) (is_open:bool) =
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
			  if acc = "" then sprintf "v = %d%s" i int_z
        else sprintf "%s || v = %d%s" acc i int_z in
		  collect_valid_repr int_z acc' t
		| (EnumFieldRange (_, i, j)) :: t ->
		  let acc' = acc in (* For now we treat enum ranges as unknown
			  (if acc = "" then acc else acc^" /\\ ")^
			  "(v < " ^ (string_of_int i) ^ int_z ^
				" \\/ v > " ^ (string_of_int j) ^ int_z ^ ")" in *)
		  collect_valid_repr int_z acc' t
		in

  let unknown_formula = collect_valid_repr int_z "" fl in
  let prime = if is_open then "" else "'" in
  let notprime = if is_open then "'" else "" in

	w i "type %s%s =\n" n prime;
	List.iter (function
	  | EnumFieldSimple (x, _) ->
		  w i "  | %s\n" (String.capitalize x)
		| _ -> ()) fl;
	w i "  | Unknown_%s of (v:%s{not (%s)})\n\n" n repr_t unknown_formula;

  (* Filter (for closed enums) *)
  if is_open then
    w o "type %s' = x:%s{not (Unknown_%s? x)}\n\n" n n n
  else
   begin
    w i "noextract let %s_filter_spec (x:%s') : GTot bool = not (Unknown_%s? x)\n\n" n n n;
    w i "let %s_filter (x:%s') : b:bool{b == %s_filter_spec x} = not (Unknown_%s? x)\n\n" n n n n;
    w i "type %s = x:%s'{%s_filter_spec x == true}\n\n" n n n
   end;

  (* Enum definition *)
	w o "inline_for_extraction let %s_enum : LP.enum %s%s %s =\n" n n notprime repr_t;
	w o "  [@inline_let] let e = [\n";
	List.iter (function
	  | EnumFieldSimple (x, i) ->
		  w o "    %s, %d%s;\n" (String.capitalize x) i int_z
		| _ -> ()) fl;
	w o "  ] in\n";
	w o "  [@inline_let] let _ =\n";
	w o "    assert_norm (L.noRepeats (LP.list_map fst e));\n";
	w o "    assert_norm (L.noRepeats (LP.list_map snd e))\n";
	w o "  in e\n\n";

  (* Interface *)
  w i "noextract val %s_parser_kind_metadata : LP.parser_kind_metadata_t\n\n" n;
  w i "noextract let %s_parser_kind = LP.strong_parser_kind %d %d %s_parser_kind_metadata\n\n" n blen blen n;
  w i "noextract val %s_parser: LP.parser %s_parser_kind %s\n\n" n n n;
  w i "inline_for_extraction val %s_parser32: LP.parser32 %s_parser\n\n" n n;
  w i "noextract val %s_serializer: LP.serializer %s_parser\n\n" n n;
  w i "inline_for_extraction val %s_serializer32: LP.serializer32 %s_serializer\n\n" n n;
  w i "inline_for_extraction val %s_size32: LP.size32 %s_serializer\n\n" n n;

  (* Synth *)
	w o "inline_for_extraction let synth_%s%s (x:LP.maybe_enum_key %s_enum) : %s%s = \n" n prime n n prime;
	w o "  match x with\n";
	w o "  | LP.Known k -> k\n";
	w o "  | LP.Unknown y ->\n";
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd %s_enum) == (%s)) in\n" n unknown_formula;
  w o "    Unknown_%s v\n\n" n;
	w o "let lemma_synth_%s%s_inj () : Lemma\n" n prime;
	w o "  (forall (x1 x2: LP.maybe_enum_key %s_enum).\n" n;
  w o "    synth_%s%s x1 == synth_%s%s x2 ==> x1 == x2) = ()\n\n" n prime n prime;
	w o "inline_for_extraction let synth_%s%s_inv (x:%s%s) : LP.maybe_enum_key %s_enum = \n" n prime n prime n;
	w o "  match x with\n";
	w o "  | Unknown_%s y ->\n" n;
	w o "    [@inline_let] let v : %s = y in\n" repr_t;
	w o "    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd %s_enum) == (%s)) in\n" n unknown_formula;
	w o "    LP.Unknown v\n";
	w o "  | x ->\n";
  w o "    [@inline_let] let x1 : %s%s = x in\n" n notprime;
  w o "    [@inline_let] let _ = assert_norm(not (Unknown_%s? x1) <==> LP.list_mem x1 (LP.list_map fst %s_enum)) in\n" n n;
  w o "    LP.Known (x1 <: LP.enum_key %s_enum)\n\n" n;
	w o "let lemma_synth_%s%s_inv () : Lemma\n" n prime;
  w o "  (forall (x: LP.maybe_enum_key %s_enum). synth_%s%s_inv (synth_%s%s x) == x) = ()\n\n" n n prime n prime;

  (* Parse *)
	w o "noextract let parse_maybe_%s_key : LP.parser _ (LP.maybe_enum_key %s_enum) =\n" n n;
  w o "  LP.parse_maybe_enum_key LP.parse_%s %s_enum\n\n" parse_t n;
	w o "noextract let serialize_maybe_%s_key : LP.serializer parse_maybe_%s_key =\n" n n;
  w o "  LP.serialize_maybe_enum_key LP.parse_%s LP.serialize_%s %s_enum\n\n" parse_t parse_t n;

  if is_open then (
    w o "let %s_kind = LP.get_parser_kind parse_maybe_%s_key\n\n" n n;
    w o "let %s_parser_kind_metadata = %s_kind.LP.parser_kind_metadata\n\n" n n;
  );

  (* Parser *)
	w o "noextract let %s%s_parser : LP.parser _ %s%s =\n" n prime n prime;
	w o "  lemma_synth_%s%s_inj ();\n" n prime;
  w o "  parse_maybe_%s_key `LP.parse_synth` synth_%s%s\n\n" n n prime;
  w o "inline_for_extraction let parse32_maybe_%s_key : LP.parser32 parse_maybe_%s_key =\n" n n;
  w o "  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_%s %s_enum parse_maybe_%s_key ())\n\n" parse_t n n;
  w o "inline_for_extraction let %s%s_parser32 : LP.parser32 %s%s_parser =\n" n prime n prime;
  w o "  lemma_synth_%s%s_inj ();\n" n prime;
  w o "  LP.parse32_synth _ synth_%s%s (fun x->synth_%s%s x) parse32_maybe_%s_key ()\n\n" n prime n prime n;

  (* Serializer *)
  w o "noextract let %s%s_serializer : LP.serializer %s%s_parser =\n" n prime n prime;
	w o "  lemma_synth_%s%s_inj ();\n  lemma_synth_%s%s_inv ();\n" n prime n prime;
	w o "  LP.serialize_synth _ synth_%s%s serialize_maybe_%s_key synth_%s%s_inv ()\n\n" n prime n n prime;
	w o "inline_for_extraction let serialize32_maybe_%s_key : LP.serializer32 serialize_maybe_%s_key =\n" n n;
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac\n";
  w o "    LP.serialize32_%s %s_enum serialize_maybe_%s_key ())\n\n" parse_t n n;
  w o "inline_for_extraction let %s%s_serializer32 : LP.serializer32 %s%s_serializer =\n" n prime n prime;
	w o "  lemma_synth_%s%s_inj ();\n  lemma_synth_%s%s_inv ();\n" n prime n prime;
  w o "  LP.serialize32_synth _ synth_%s%s _ serialize32_maybe_%s_key synth_%s%s_inv (fun x->synth_%s%s_inv x) ()\n\n" n prime n n prime n prime;

  (* Filter *)
  if not is_open then
   begin
    w o "noextract let %s_kind = LP.parse_filter_kind (LP.get_parser_kind %s'_parser)\n\n" n n;
    w o "let %s_parser_kind_metadata = %s_kind.LP.parser_kind_metadata\n\n" n n;
    w o "let %s_parser = LP.parse_filter %s'_parser %s_filter_spec\n\n" n n n;
    w o "let %s_parser32 = LP.parse32_filter %s'_parser32 %s_filter_spec %s_filter\n\n" n n n n;
    w o "let %s_serializer = LP.serialize_filter %s'_serializer %s_filter_spec\n\n" n n n;
    w o "let %s_serializer32 = LP.serialize32_filter %s'_serializer32 %s_filter_spec\n\n" n n n;
   end;

  w o "let %s_size32 =\n" n;
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond %s_serializer %dul) in\n" n blen;
  w o "  LP.size32_constant %s_serializer %dul ()\n\n" n blen;
	()

and compile_select o i n sel fl =
  let fcase (case, ctx) =
    let n = n ^ "_" ^ case in
    let depl, li = dep_len (Struct (n, [], ctx)) in
    compile_struct o i n ctx
    in
  List.iter fcase fl;
  w i "type %s =\n" n;
  List.iter (fun (case, _) -> w i "  | %s of %s_%s\n" (String.capitalize case) n case) fl;
  w i "\n"
*)

let compile o i (p:gemstone_t) =
  let n = tname p in
  let (fst, fsti) = !headers in

  (* .fsti *)
  w i "module %s%s\n\n" !prefix n;
  w i "open %s\n" !bytes;

(*
  let depl, li = dep_len p in
  let depl = List.filter (fun x -> not (basic_type x)) depl in
  let depl = List.map (fun s -> !prefix ^ (String.uncapitalize s)) depl in
  (List.iter (w i "open %s\n") depl);
  w i "\n";
*)

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
  (* (List.iter (w o "open %s\n") depl); *)
  w o "\n";

  w o "module U8 = FStar.UInt8\n";
  w o "module U16 = FStar.UInt16\n";
  w o "module U32 = FStar.UInt32\n";
	w o "module LP = LowParse.SLow\n";
	w o "module L = FStar.List.Tot\n";
  (List.iter (w o "%s\n") (List.rev fst));
  w o "\n";

	w o "#reset-options \"--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2\"\n\n";
	match p with
	| Enum(attr, fl, n) ->  () (*compile_enum o i n fl (List.mem "open" attr)*)
  | Struct(attr, fl, n) -> () (*compile_struct o i n fl *)
  | Typedef(attr, ty, n, vec, def) -> () (*compile_select o i n sel fl*)

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
