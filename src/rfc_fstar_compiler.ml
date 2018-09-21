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
let linfo : len_info SM.t ref = ref SM.empty

(* Storage of inlined types *)
let inliners: gemstone_t SM.t ref = ref SM.empty

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

let attr_of = function
  | Enum (a, _, _) -> a
  | Struct (a, _, _) -> a
  | Typedef (a, _, _, _, _) -> a

let has_attr (a:attr list) (s:attr) = List.mem s a

let get_leninfo (t:typ) =
  try SM.find (String.uncapitalize t) !linfo
  with _ -> failwith ("Failed lookup for type "^t)

let li_add (s:string) (li:len_info) =
  printf "LINFO<%s>: vl=%s lenLen=%d minLen=%d maxLen=%d minCount=%d maxCount=%d\n"
    s (if li.vl then "yes" else "no") li.len_len li.min_len li.max_len li.min_count li.max_count;
  if SM.mem s !linfo then failwith (sprintf "Duplicate type definition: %s\n" s);
  linfo := SM.add s li !linfo

let basic_type = function
  | "opaque" | "uint8" | "uint16" | "uint24" | "uint32" -> true
  | _ -> false

let rec sizeof = function
  | TypeSelect(n, cl, def) ->
    let lil = (List.map (fun (_,ty) -> get_leninfo ty) cl)
              @ (match def with None -> [] | Some ty -> [get_leninfo ty]) in
    let li = { len_len = 0; min_len = max_int; max_len = 0; min_count = 0; max_count = 0; vl = false; } in
    List.iter (fun l ->
      li.min_len <- min li.min_len l.min_len;
      li.max_len <- max li.max_len l.max_len;
      if l.vl then li.vl <- true;
    ) lil; li
  | TypeSimple typ ->
    match typ with
    | "opaque"
    | "uint8"  -> { len_len = 0; min_len = 1; max_len = 1; min_count = 0; max_count = 0; vl = false; }
    | "uint16" -> { len_len = 0; min_len = 2; max_len = 2; min_count = 0; max_count = 0; vl = false; }
    | "uint24" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; }
    | "uint32" -> { len_len = 0; min_len = 4; max_len = 4; min_count = 0; max_count = 0; vl = false; }
    | s ->
      let li = get_leninfo s in
      {li with len_len = li.len_len} (* shallow copy *)

let abs (n:typ) =
	!prefix ^ (String.uncapitalize n)

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

let add_field (tn:typ) (n:field) (ty:type_t) (v:vector_t) =
  let qname = if tn = "" then n else tn^"@"^n in
  let li = sizeof ty in
  let li' =
    match v with
    | VectorNone -> li
    | VectorFixed k ->
      {li with
        min_len = k;
        max_len = k;
        min_count = k / li.min_len;
        max_count = k / li.max_len;
      }
    | VectorVldata tn ->
      let (len_len, max_len) = match tn with
        | "uint8" -> 1, 256 | "uint16" -> 2, 65536
        | "uint24" -> 3, 16777216 | "uint32" -> 4, 4294967296
        | _ -> failwith "bad vldata" in
      {li with min_len = len_len; max_len = max_len; vl = true; }
    | VectorSymbolic cst ->
      if tn = "" then failwith "Can't define a symbolic bytelen outide struct";
      get_leninfo (tn^"@"^cst)
    | VectorRange (low, high) ->
      let h = log256 high in
      (if li.len_len + li.max_len = 0 then failwith ("Can't compute count bound on "^tn));
      { li with
        vl = true;
        min_count = low / (li.len_len + li.max_len);
        max_count = high / (li.len_len + li.min_len);
        len_len = h;
        min_len = h + low;
        max_len = h + high; }
      in
    li_add qname li'

let typedep = function
  | TypeSimple ty -> [ty]
  | TypeSelect (_, l, o) ->
    let l = List.map (fun (_, ty)->ty) l in
    match o with None -> l | Some ty -> ty :: l

let dedup l =
  let r = ref [] in
  List.iter (fun x -> if not (List.mem x !r) then r := x::!r) l;
  List.rev !r

let getdep (p:gemstone_t) : typ list =
  let tn = tname p in
  let dep =
    match p with
    | Enum (_, fl, n) ->
      let m = try List.find (function EnumFieldAnonymous x -> true | _ -> false) fl
              with _ -> failwith ("Enum "^n^" is missing a representation hint") in
      let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; } in
      (match m with
      | EnumFieldAnonymous 255 -> li.min_len <- 1; li.max_len <- 1
      | EnumFieldAnonymous 65535 -> li.min_len <- 2; li.max_len <- 2
      | EnumFieldAnonymous 4294967295 -> li.min_len <- 4; li.max_len <- 4);
      li_add tn li; ([]:typ list list)
    | Struct (_, fl, _) ->
      let li = { len_len = 0; min_len = 0; max_len = 0; min_count = 0; max_count = 0;  vl = false; } in
      let dep = List.map (fun (al, ty, n, vec, def) ->
        add_field tn n ty vec;
        let lif = get_leninfo (tn^"@"^n) in
        li.vl <- li.vl || lif.vl;
        li.min_len <- li.min_len + lif.min_len;
        li.max_len <- li.max_len + lif.max_len;
        typedep ty) fl in
      li_add tn li; dep
    | Typedef (al, ty, n, vec, def) ->
      add_field "" (String.uncapitalize n) ty vec;
      [typedep ty]
    in
  dedup (List.flatten dep)

let write_api c n bmin bmax =
  w c "noextract val %s_parser_kind_metadata : LP.parser_kind_metadata_t\n\n" n;
  w c "noextract let %s_parser_kind = LP.strong_parser_kind %d %d %s_parser_kind_metadata\n\n" n bmin bmax n;
  w c "noextract val %s_parser: LP.parser %s_parser_kind %s\n\n" n n n;
  w c "noextract val %s_serializer: LP.serializer %s_parser\n\n" n n;
  w c "noextract let %s_bytesize (x:%s) : GTot nat = Seq.length (%s_serializer x)\n\n" n n n;
  w c "inline_for_extraction val %s_parser32: LP.parser32 %s_parser\n\n" n n;
  w c "inline_for_extraction val %s_serializer32: LP.serializer32 %s_serializer\n\n" n n;
  w c "inline_for_extraction val %s_size32: LP.size32 %s_serializer\n\n" n n

let rec compile_enum o i n (fl: enum_field_t list) (al:attr list) =
  let is_open = has_attr al "open" in

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

  (* Used in select() *)
  w o "noextract let %s_repr_parser = %s\n\n" n (pcombinator_name repr_t);
  w o "noextract let %s_repr_serializer = %s\n\n" n (scombinator_name repr_t);
  w o "noextract let %s_repr_parser32 = %s\n\n" n (pcombinator32_name repr_t);
  w o "noextract let %s_repr_serializer32 = %s\n\n" n (scombinator32_name repr_t);

  write_api i n blen blen;

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

  (* Spec *)
	w o "noextract let %s%s_parser : LP.parser _ %s%s =\n" n prime n prime;
	w o "  lemma_synth_%s%s_inj ();\n" n prime;
  w o "  parse_maybe_%s_key `LP.parse_synth` synth_%s%s\n\n" n n prime;
  w o "noextract let %s%s_serializer : LP.serializer %s%s_parser =\n" n prime n prime;
	w o "  lemma_synth_%s%s_inj ();\n  lemma_synth_%s%s_inv ();\n" n prime n prime;
	w o "  LP.serialize_synth _ synth_%s%s serialize_maybe_%s_key synth_%s%s_inv ()\n\n" n prime n n prime;

  (* Intermediate *)
  w o "inline_for_extraction let parse32_maybe_%s_key : LP.parser32 parse_maybe_%s_key =\n" n n;
  w o "  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_%s %s_enum)\n\n" parse_t n;
  w o "inline_for_extraction let %s%s_parser32 : LP.parser32 %s%s_parser =\n" n prime n prime;
  w o "  lemma_synth_%s%s_inj ();\n" n prime;
  w o "  LP.parse32_synth _ synth_%s%s (fun x->synth_%s%s x) parse32_maybe_%s_key ()\n\n" n prime n prime n;
	w o "inline_for_extraction let serialize32_maybe_%s_key : LP.serializer32 serialize_maybe_%s_key =\n" n n;
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac\n";
  w o "    LP.serialize32_%s %s_enum)\n\n" parse_t n;
  w o "inline_for_extraction let %s%s_serializer32 : LP.serializer32 %s%s_serializer =\n" n prime n prime;
	w o "  lemma_synth_%s%s_inj ();\n  lemma_synth_%s%s_inv ();\n" n prime n prime;
  w o "  LP.serialize32_synth _ synth_%s%s _ serialize32_maybe_%s_key synth_%s%s_inv (fun x->synth_%s%s_inv x) ()\n\n" n prime n n prime n prime;

  (* Filter *)
  if not is_open then
   begin
    w o "noextract let %s_kind = LP.parse_filter_kind (LP.get_parser_kind %s'_parser)\n\n" n n;
    w o "noextract let %s_parser_kind_metadata = %s_kind.LP.parser_kind_metadata\n\n" n n;
    w o "noextract let %s_parser = LP.parse_filter %s'_parser %s_filter_spec\n\n" n n n;
    w o "noextract let %s_serializer = LP.serialize_filter %s'_serializer %s_filter_spec\n\n" n n n;
    w o "let %s_parser32 = LP.parse32_filter %s'_parser32 %s_filter_spec %s_filter\n\n" n n n n;
    w o "let %s_serializer32 = LP.serialize32_filter %s'_serializer32 %s_filter_spec\n\n" n n n;
   end;

  w o "let %s_size32 =\n" n;
  w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond %s_serializer %dul) in\n" n blen;
  w o "  LP.size32_constant %s_serializer %dul ()\n\n" n blen;
	()

and compile_select o i n tagn tagt taga cl def al =
  let ip = if has_attr al "private" then o else i in
  let isopen = not (def = None) in
  let li = get_leninfo n in
  w o "friend %s\n\n" (abs tagt);
  w i "type %s =\n" n;
  List.iter (fun (case, ty) -> w i "  | Case_%s of %s\n" case (compile_type ty)) cl;
  w i "\n\ninline_for_extraction let tag_of_%s (x:%s) : %s = match x with\n" n n (compile_type tagt);
  List.iter (fun (case, ty) -> w i "  | Case_%s _ -> %s\n" case (String.capitalize case)) cl;
  (match def with Some t -> w o "let " | None -> ());
  w i "\n";
  write_api ip n li.min_len li.max_len;
  w o "let %s_sum = LP.make_sum %s_enum tag_of_%s\n\n" n (compile_type tagt) n;

  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    let ty0 = compile_type ty in
    w o "inline_for_extraction let synth_case_%s (z:%s) : Tot (LP.sum_cases %s_sum %s) =\n" cn ty0 n cn;
    w o "  [@inline_let] let res : %s = Case_%s z in\n" n case;
    w o "  [@inline_let] let _ = assert_norm (LP.sum_tag_of_data %s_sum res == %s) in\n" n cn;
    w o "  res\n\n";
    w o "let synth_case_%s_inj () : Lemma (LP.synth_injective synth_case_%s) = ()\n\n" cn cn;
    w o "let parse_case_%s : LP.parser _ (LP.sum_cases %s_sum %s) =\n" cn n cn;
    w o "  synth_case_%s_inj (); LP.parse_synth %s synth_case_%s\n\n" cn (pcombinator_name ty0) cn
  ) cl;

  w o "let parse_%s_cases' (x:LP.sum_key %s_sum)\n" n n;
  w o "  : Tot (k:LP.parser_kind & LP.parser k  (LP.sum_cases %s_sum x))\n" n;
  w o "  = match x with\n";
  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    w o "  | %s -> (| _, parse_case_%s |)\n" cn cn;
  ) cl;

  w o "\nprivate let parse_%s_cases: x:LP.sum_key %s_sum -> LP.parser _ (LP.sum_cases %s_sum x)\n" n n n;
  w o "  = LP.parse_sum_cases %s_sum parse_%s_cases'\n\n" n n;
  w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
  w o "let %s_parser' = LP.parse_sum %s_sum %s_repr_parser parse_%s_cases\n\n" n n (compile_type tagt) n;
  w o "let %s_parser =\n" n;
  w o "  assert_norm (LP.get_parser_kind %s_parser' == %s_parser_kind);\n" n n;
  w o "  %s_parser'\n\n" n;

  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    let ty0 = compile_type ty in
    w o "inline_for_extraction let synth_case_%s_inv (z:LP.sum_cases %s_sum %s) : %s =\n" cn n cn ty0;
    w o "  [@inline_let] let z' : %s = z in\n" n;
    w o "  assert(Case_%s? z' <==> tag_of_%s z' == %s);\n" case n cn;
    w o "  match z' with | Case_%s res -> res\n\n" case;
    w o "#set-options \"--z3rlimit 30\"\n";
    w o "let synth_case_%s_inv_correct () : Lemma\n" cn;
    w o "  (LP.synth_inverse synth_case_%s synth_case_%s_inv) = ()\n" cn cn;
    w o "#reset-options\n\n";
    w o "let serialize_case_%s : LP.serializer parse_case_%s =\n" cn cn;
    w o "  synth_case_%s_inj (); synth_case_%s_inv_correct ();\n" cn cn;
    w o "  LP.serialize_synth %s synth_case_%s %s synth_case_%s_inv ()\n\n"
      (pcombinator_name ty0) cn (scombinator_name ty0) cn
  ) cl;

  w o "#set-options \"--z3rlimit 30\"\n";
  w o "let serialize_%s_cases' (x:LP.sum_key %s_sum)\n" n n;
  w o "  : LP.serializer (dsnd (parse_%s_cases' x)) =\n" n;
  w o "  match x with\n";
  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    w o "  | %s -> serialize_case_%s\n" cn cn
  ) cl;
  w o "#reset-options\n\n";

  w o "let serialize_%s_cases: x:LP.sum_key %s_sum -> LP.serializer (parse_%s_cases x)\n" n n n;
  w o "  = LP.serialize_sum_cases %s_sum parse_%s_cases' serialize_%s_cases'\n\n" n n n;
  w o "let %s_serializer' : LP.serializer %s_parser' =\n" n n;
  w o "  LP.serialize_sum %s_sum %s_repr_serializer serialize_%s_cases\n\n" n (compile_type tagt) n;
  w o "let %s_serializer =\n" n;
  w o "  assert_norm (LP.get_parser_kind %s_parser' == %s_parser_kind);\n" n n;
  w o "  %s_serializer'\n\n" n;

  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    let ty0 = compile_type ty in
    w o "inline_for_extraction let parse32_case_%s : (LP.parser32 parse_case_%s) =\n" cn cn;
    w o "  [@inline_let] let _ = synth_case_%s_inj () in\n" cn;
    w o "  LP.parse32_synth _ synth_case_%s (fun x -> synth_case_%s x) %s ()\n\n" cn cn (pcombinator32_name ty0);
    w o "inline_for_extraction let serialize32_case_%s : (LP.serializer32 serialize_case_%s) =\n" cn cn;
    w o "  [@inline_let] let _ = synth_case_%s_inj (); synth_case_%s_inv_correct () in\n" cn cn;
    w o "  LP.serialize32_synth _ synth_case_%s _ %s synth_case_%s_inv (fun x->synth_case_%s_inv x) ()\n\n" cn (scombinator32_name ty0) cn cn
  ) cl;

  w o "#set-options \"--z3rlimit 30\"\n";
  w o "inline_for_extraction let parse32_%s_cases' (x: LP.sum_key %s_sum)\n" n n;
  w o "  : Tot (LP.parser32 (dsnd (parse_%s_cases' x))) =\n" n;
  w o "  match x with\n";
  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    w o "  | %s -> parse32_case_%s\n" cn cn
  ) cl;
  w o "#reset-options\n\n";

  w o "inline_for_extraction let parse32_%s_cases\n" n;
  w o "  : x:LP.sum_key %s_sum -> LP.parser32 (parse_%s_cases x) =\n" n n;
  w o "  LP.parse32_sum_cases %s_sum parse_%s_cases' parse32_%s_cases'\n\n" n n n;

  w o "#set-options \"--z3rlimit 30\"\n";
  w o "let serialize32_%s_cases' (x: LP.sum_key %s_sum)\n" n n;
  w o "  : Tot (LP.serializer32 (serialize_%s_cases' x)) =\n" n;
  w o "  assume false; // FIXME\nmatch x with\n";
  List.iter (fun (case, ty) ->
    let cn = String.capitalize case in
    w o "  | %s -> serialize32_case_%s\n" cn cn
  ) cl;
  w o "#reset-options\n\n";

  w o "inline_for_extraction let serialize32_%s_cases\n" n;
  w o "  : x:LP.sum_key %s_sum -> LP.serializer32 (serialize_%s_cases x) =\n" n n;
  w o "  LP.serialize32_sum_cases %s_sum parse_%s_cases' _ serialize32_%s_cases'\n\n" n n n;

  w o "inline_for_extraction let destr_%s_enum (t:Type)\n" (compile_type tagt);
  w o "  : LP.enum_destr_t t %s_enum = _ by (LP.enum_destr_tac %s_enum)\n\n" (compile_type tagt) (compile_type tagt);

  w o "let parse_%s_key : LP.parser _ (LP.enum_key %s_enum) =\n" (compile_type tagt) (compile_type tagt);
  w o "  LP.parse_enum_key %s_repr_parser %s_enum\n\n" (compile_type tagt) (compile_type tagt);

  w o "inline_for_extraction let parse32_%s_key : LP.parser32 parse_%s_key =\n" (compile_type tagt) (compile_type tagt);
  w o "  FStar.Tactics.synth_by_tactic (LP.parse32_enum_key_tac %s_repr_parser32 %s_enum)\n\n" (compile_type tagt) (compile_type tagt);

  w o "let serialize_%s_key : LP.serializer parse_%s_key =\n" (compile_type tagt) (compile_type tagt);
  w o "  LP.serialize_enum_key _ %s_repr_serializer %s_enum\n\n" (compile_type tagt) (compile_type tagt);

  w o "inline_for_extraction let serialize32_%s_key : LP.serializer32 serialize_%s_key =\n" (compile_type tagt) (compile_type tagt);
  w o "  FStar.Tactics.synth_by_tactic (LP.serialize32_enum_key_gen_tac %s_repr_serializer32 %s_enum)\n\n" (compile_type tagt) (compile_type tagt);

  w o "let %s_parser32' =\n" n;
  w o "  LP.parse32_sum_gen' #_ %s_sum %s_repr_parser parse32_%s_cases\n" n (compile_type tagt) n;
  w o "    parse32_%s_key (destr_tag_enum (LP.parse32_sum_t %s_sum))\n\n" (compile_type tagt) n;
  w o "let %s_parser32 =\n" n;
  w o "  assert_norm (LP.get_parser_kind %s_parser' == %s_parser_kind);\n" n n;
  w o "  %s_parser32'\n\n" n;

  w o "let %s_serializer32' =\n" n;
  w o "  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind %s_repr_parser)" (compile_type tagt);
  w o " (LP.weaken_parse_cases_kind %s_sum parse_%s_cases'));\n" n n;
  w o "  LP.serialize32_sum_gen' %s_sum serialize32_%s_key\n" n (compile_type tagt);
  w o "    serialize32_%s_cases () (fun x -> %s_of_%s x)\n\n" n (compile_type tagt) n;
  w o "let %s_serializer32 =\n" n;
  w o "  assert_norm (LP.get_parser_kind %s_parser' == %s_parser_kind);\n" n n;
  w o "  %s_serializer32'\n\n" n;
  ()

and compile_typedef o i tn fn (ty:type_t) vec def al =
  let n = if tn = "" then String.uncapitalize fn else tn^"_"^fn in
  let qname = if tn = "" then String.uncapitalize fn else tn^"@"^fn in
  let ip = if has_attr al "private" then o else i in
  let li = get_leninfo qname in
  match ty with
  | TypeSelect (sn, cl, def) ->  () (*failwith "Unsupported select"*)
  | TypeSimple ty ->
    let ty0 = compile_type ty in
    match vec with
    (* Type aliasing *)
    | VectorNone ->
      w i "type %s = %s\n\n" n ty0;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "noextract let %s_parser = %s\n\n" n (pcombinator_name ty0);
      w o "noextract let %s_serializer = %s\n\n" n (scombinator_name ty0);
      w o "inline_for_extraction let %s_parser32 = %s\n\n" n (pcombinator32_name ty0);
      w o "inline_for_extraction let %s_serializer32 = %s\n\n" n (scombinator32_name ty0);
      w o "inline_for_extraction let %s_size32 = %s\n\n" n (size32_name ty0)

    (* Should be replaced with Vldata during normalization *)
    | VectorSymbolic cst -> failwith "not supported"

    | VectorVldata vl ->
      let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
      w i "noextract val %s_bytesize: %s -> GTot nat\n\n" n ty0;
      w o "let %s_bytesize x = Seq.length (LP.serialize %s x)\n\n" n (scombinator_name ty0);
      w i "type %s = x:%s{let l = %s_bytesize x in %d <= l /\\ l <= %d}\n\n" n ty0 n min max;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d %s\n\n" n min max (scombinator_name ty0);
      w o "let _ = assert_norm (%s' == %s)\n\n" n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_bounded_vldata_strong %d %d %s\n\n" min max (scombinator_name ty0);
      w o "let %s_parser = %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_bounded_vldata_strong %d %d %s\n\n" min max (scombinator_name ty0);
      w o "let %s_serializer = %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul %s %s\n\n" min min max max (scombinator_name ty0) (pcombinator32_name ty0);
      w o "let %s_parser32 = %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_bounded_vldata_strong %d %d %s\n\n" min max (scombinator32_name ty0);
      w o "let %s_serializer32 = %s'_serializer32\n\n" n n;
      w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      (* assert_norm to be removed when moved to LowParse *)
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";
      w o "  LP.size32_bounded_vldata_strong %d %d %s %dul\n\n" min max (size32_name ty0) li.len_len;
      w o "let %s_size32 = %s'_size32\n\n" n n

    (* Fixed-length bytes *)
    | VectorFixed k when ty0 = "U8.t" ->
      w i "type %s = lbytes %d\n\n" n k;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = {LP.parser_kind_metadata_total = true}\n\n" n;
      w o "noextract let %s_parser = LP.parse_flbytes %d\n\n" n k;
      w o "noextract let %s_serializer = LP.serialize_flbytes %d\n\n" n k;
      w o "inline_for_extraction let %s_parser32 = LP.parse32_flbytes %d %dul\n\n" n k k;
      w o "inline_for_extraction let %s_serializer32 = LP.serialize32_flbytes %d\n\n" n k;
      w o "inline_for_extraction let %s_size32 = LP.size32_constant %s_serializer %dul ()\n\n" n n k;

    (* Fixed length list *)
    | VectorFixed k when li.min_len = li.max_len ->
      w i "type %s = l:list %s{L.length l == %d}\n\n" n ty0 li.min_count;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "type %s' = LP.array %s %d\n\n" n ty0 li.min_count;
      w o "private let eq () : Lemma (%s' == %s) =\n" n n;
      w o "  assert(%s'==%s) by (FStar.Tactics.norm [delta_only [`%%(LP.array); `%%(%s); `%%(%s')]])\n\n" n n n n;
      w o "noextract let %s'_parser = LP.parse_array %s %d %d\n\n" n (scombinator_name ty0) k li.min_count;
      w o "let %s_parser = eq(); LP.coerce _ %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer = LP.serialize_array %s %d %d ()\n\n" n (scombinator_name ty0) k li.min_count;
      w o "let %s_serializer = eq(); LP.coerce _ %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 = LP.parse32_array %s %s %d %dul %d ()\n\n"
        n (scombinator_name ty0) (pcombinator32_name ty0) k k li.min_count;
      w o "let %s_parser32 = eq(); LP.coerce _ %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 =\n" n;
      w o "  LP.serialize32_array #_ #_ #_ #%s %s %d %d ()\n\n" (scombinator_name ty0) (scombinator32_name ty0) k li.min_count;
      w o "let %s_serializer32 = eq(); LP.coerce _ %s'_serializer32\n\n" n n;
      w o "let %s_size32 = LP.size32_array %s %d %dul %d ()\n" n (scombinator_name ty0) k k li.min_count

    (* Fixed bytelen list of variable length elements *)
    | VectorFixed(k) ->
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n ty0;
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty0);
      w i "type %s = l:list %s{%s_list_bytesize == %d}\n\n" n ty0 n k;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "type %s' = LP.parse_fldata_strong_t (LP.serialize_list _ %s) %d\n\n" n (scombinator_name ty0) k;
      w o "let _ = assert_norm (%s' == %s)\n\n" n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty0) k;
      w o "let %s_parser = %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_fldata_strong (LP.serialize_list _ %s) %d\n\n" (scombinator_name ty0) k;
      w o "let %s_serializer = %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_fldata_strong (LP.serialize_list _ %s) (LP.parse32_list %s) %d %dul\n\n" (scombinator_name ty0) (pcombinator32_name ty0) k k;
      w o "let %s_parser32 = %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_fldata_strong (LP.partial_serialize32_list _ %s %s ()) %d\n\n" (scombinator_name ty0) (scombinator32_name ty0) k;
      w o "let %s_serializer32 = %s'_serializer32\n\n" n n;
      w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      w o "  LP.size32_fldata_strong (LP.serialize_list _ %s) %d %dul\n\n" (scombinator_name ty0) k k;
      w o "let %s_size32 = %s'_size32\n\n" n n

    (* Variable length bytes *)
    | VectorRange (low, high) when ty0 = "U8.t" ->
      w i "type %s = b:bytes{%d <= length b /\\ length b <= %d}\n\n" n low high;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "noextract let %s_parser = LP.parse_bounded_vlbytes %d %d\n\n" n low high;
      w o "noextract let %s_serializer = LP.serialize_bounded_vlbytes %d %d\n\n" n low high;
      w o "inline_for_extraction let %s_parser32 = LP.parse32_bounded_vlbytes %d %dul %d %dul\n\n" n low low high high;
      w o "inline_for_extraction let %s_serializer32 = LP.serialize32_bounded_vlbytes %d %d\n\n" n low high;
      w o "inline_for_extraction let %s_size32 = LP.size32_bounded_vlbytes %d %d %dul\n\n" n low high (log256 high)

    (* Variable length list of fixed-length elements *)
    | VectorRange (low, high) when li.min_len = li.max_len ->
      w i "type %s = l:list %s{%d <= L.length l /\\ L.length l <= %d}" n ty0 li.min_count li.max_count;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "let %s_parser =\n" n;
      w o "  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond %d %d %s %d %d == true) in\n" low high (pcombinator_name ty0) li.min_count li.max_count;
      w o "  LP.parse_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      w o "let %s_serializer =\n" n;
      w o "  LP.serialize_vlarray %d %d %s %d %d ()\n\n" low high (scombinator_name ty0) li.min_count li.max_count;
      w o "let %s_parser32 =\n" n;
      w o "  LP.parse32_vlarray %d %dul %d %dul %s %s %d %d ()\n\n" low low high high (scombinator_name ty0) (pcombinator32_name ty0) li.min_count li.max_count;
      w o "let %s_serializer32 =\n" n;
      w o "  LP.serialize32_vlarray %d %d %s %d %d ()\n\n" low high (scombinator32_name ty0) li.min_count li.max_count;
      w o "let %s_size32 =\n" n;
      w o "  LP.size32_vlarray %d %d %s %d %d () %dul %dul\n\n" low high (scombinator_name ty0) li.min_count li.max_count li.len_len li.min_len

    (* Variable length list of variable length elements *)
    | VectorRange(low, high) ->
      let (min, max) = (li.min_len-li.len_len), (li.max_len-li.len_len) in
      w i "noextract val %s_list_bytesize: list %s -> GTot nat\n\n" n ty0;
      w o "let %s_list_bytesize x = Seq.length (LP.serialize (LP.serialize_list _ %s) x)\n\n" n (scombinator_name ty0);
      w i "type %s = l:list %s{let x = %s_list_bytesize l in %d <= x /\\ x <= %d}\n\n" n ty0 n min max;
      write_api ip n li.min_len li.max_len;
      w o "noextract let %s_parser_kind_metadata = LP.default_parser_kind.LP.parser_kind_metadata\n\n" n;
      w o "type %s' = LP.parse_bounded_vldata_strong_t %d %d (LP.serialize_list _ %s)\n\n" n min max (scombinator_name ty0);
      w o "let _ = assert_norm (%s' == %s)\n\n" n n;
      w o "noextract let %s'_parser : LP.parser _ %s' =\n" n n;
      w o "  LP.parse_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty0);
      w o "let %s_parser = %s'_parser\n\n" n n;
      w o "noextract let %s'_serializer : LP.serializer %s'_parser =\n" n n;
      w o "  LP.serialize_bounded_vldata_strong %d %d (LP.serialize_list _ %s)\n\n" min max (scombinator_name ty0);
      w o "let %s_serializer = %s'_serializer\n\n" n n;
      w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
      w o "  LP.parse32_bounded_vldata_strong %d %dul %d %dul (LP.serialize_list _ %s) (LP.parse32_list %s)\n\n" min min max max (scombinator_name ty0) (pcombinator32_name ty0);
      w o "let %s_parser32 = %s'_parser32\n\n" n n;
      w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
      w o "  LP.serialize32_bounded_vldata_strong %d %d (LP.partial_serialize32_list _ %s %s ())\n\n" min max (scombinator_name ty0) (scombinator32_name ty0);
      w o "let %s_serializer32 = %s'_serializer32\n\n" n n;
      w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
      (* assert_norm to be removed when moved to LowParse *)
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u32 4ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u16 2ul) in\n";
      w o "  [@inline_let] let _ = assert_norm (LP.size32_constant_precond LP.serialize_u8 1ul) in\n";
      w o "  LP.size32_bounded_vldata_strong %d %d (LP.size32_list %s ()) %dul\n\n" min max (size32_name ty0) li.len_len;
      w o "let %s_size32 = %s'_size32\n\n" n n

and compile_struct o i n (fl: struct_field_t list) (al:attr list) =
  let li = get_leninfo n in

  (* Hoist all constructed types (select, vector, etc) into
     sub-definitions using private attribute in implementation *)
  let fields = List.map (fun (al, ty, fn, vec, def) ->
    let fn0 = String.uncapitalize fn in
    match ty, vec with
    | TypeSimple ty0, VectorNone ->
      (fn0, compile_type ty0)
    | _ ->
      compile_typedef o i n fn ty vec def ("private"::al);
      (fn0, sprintf "%s_%s" n fn)) fl in

  (* application type *)
  if fields = [] then
    w i "type %s = lbytes 0\n\n" n
  else
   begin
    w i "type %s = {\n" n;
    List.iter (fun (fn, ty) ->
      w i "  %s : %s;\n" fn ty) fields;
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

  (* Write parser API *)
  write_api i n li.min_len li.max_len;

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

  w o "noextract let %s'_parser_kind = LP.get_parser_kind %s'_parser\n\n" n n;
  w o "let %s_parser_kind_metadata = %s'_parser_kind.LP.parser_kind_metadata\n\n" n n;
  w o "let %s_parser =\n  synth_%s_injective ();\n  assert_norm (%s_parser_kind == %s'_parser_kind);\n" n n n n;
  w o "  %s'_parser `LP.parse_synth` synth_%s\n\n" n n;

  (* main parser32 *)
  w o "inline_for_extraction let %s'_parser32 : LP.parser32 %s'_parser =\n" n n;
  if fields = [] then w o "  LP.parse32_flbytes 0 0ul";
  let tuple = List.fold_left (
    fun acc (fn, ty) ->
      let c = pcombinator32_name ty in
      if acc="" then c else sprintf "%s\n  `LP.parse32_nondep_then` %s" acc c
    ) "" fields in
  w o "  %s\n\n" tuple;
  w o "inline_for_extraction let %s_parser32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.parse32_synth _ synth_%s (fun x -> synth_%s x) %s'_parser32 ()\n\n" n n n;

  (* main serializer type *)
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
  w o "inline_for_extraction let %s'_serializer32 : LP.serializer32 %s'_serializer =\n" n n;
  if fields = [] then w o "  LP.serialize32_flbytes 0";
  let tuple = List.fold_right (
    fun (fn, ty) acc ->
      let c = scombinator32_name ty in
      if acc="" then c else sprintf "LP.serialize32_nondep_then (%s) ()\n  %s ()" acc c
    ) (List.rev fields) "" in
  w o "  %s\n\n" tuple;

  w o "inline_for_extraction let %s_serializer32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.serialize32_synth _ synth_%s _ %s'_serializer32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;

  (* size32, the assert_norms should move to LP *)
  w o "inline_for_extraction let %s'_size32 : LP.size32 %s'_serializer =\n" n n;
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

  w o "let %s_size32 =\n  [@inline_let] let _ = synth_%s_injective () in\n" n n;
  w o "  [@inline_let] let _ = synth_%s_inverse () in\n" n;
  w o "  [@inline_let] let _ = assert_norm (%s_parser_kind == %s'_parser_kind) in\n" n n;
  w o "  LP.size32_synth _ synth_%s _ %s'_size32 synth_%s_recip (fun x -> synth_%s_recip x) ()\n\n" n n n n;
  ()

(* Rewrite {... uintX len; t value[len]; ...} into VectorVldata *)
let rec normalize_symboliclen o i sn (fl:struct_field_t list) : struct_field_t list =
  match fl with
  | [] -> []
  | (al, TypeSimple(tagt), tagn, VectorNone, None)
    :: (al', ty, n, VectorSymbolic k, None) :: r
    when tagn = k ->
      let h =
        match ty with
        | TypeSimple ty -> (al @ al', TypeSimple ty, n, VectorVldata tagt, None)
        | TypeSelect (sel, cl, def) ->
          let cl' = List.map (fun (c,t)->
            let etyp = sprintf "%s_%s_case_%s" sn n c in
            add_field "" etyp (TypeSimple t) (VectorVldata tagt);
            compile_typedef o i "" etyp (TypeSimple t) (VectorVldata tagt) None ("private"::al);
            (c, etyp)
          ) cl in
          let def' = match def with
            | None -> None
            | Some ty ->
              let etyp = sprintf "%s_%s_default" sn n in
              add_field "" etyp (TypeSimple ty) (VectorVldata tagt);
              compile_typedef o i "" etyp (TypeSimple ty) (VectorVldata tagt) None ("private"::al);
              Some etyp
            in
          (al @ al', TypeSelect(sel, cl', def'), n, VectorNone, None)
        in
      h :: (normalize_symboliclen o i sn r)
  | h :: t -> h :: (normalize_symboliclen o i sn t)

let compile o i (p:gemstone_t) =
  let n = tname p in
  let (fst, fsti) = !headers in

  (* .fsti *)
  w i "module %s%s\n\n" !prefix n;
  w i "open %s\n" !bytes;

  let depl = getdep p in
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
	| Enum(al, fl, _) ->  compile_enum o i n fl al
  | Struct(al, fl, _) ->
    let fl = normalize_symboliclen o i n fl in
    (match fl with
    | [ (al, TypeSimple(tagt), tagn, VectorNone, None);
        (al', TypeSelect (tagn', cases, def), seln, VectorNone, None) ] ->
        compile_select o i n tagn tagt al cases def al'
    | fl -> compile_struct o i n fl al)
  | Typedef(al, ty, _, vec, def) -> compile_typedef o i "" n ty vec def al

let compile_inline o i (p:gemstone_t) =
  if has_attr (attr_of p) "inline" then (
    printf "Warning: type %s will be inlined at use site!\n" (tname p);
    inliners := SM.add (tname p) p !inliners
  ) else compile o i p

let rfc_generate_fstar (p:Rfc_ast.prog) =
  let aux (p:gemstone_t) =
	  let n = tname p in
		let fn = sprintf "%s/%s%s.fst" !odir !prefix n in
	  printf "Writing parsers for type <%s> to <%s>...\n" n fn;
		let o, i = try open_out fn, open_out (fn^"i")
               with _ -> failwith "Failed to create output file" in
		compile_inline o i p;
    close_out o
	in List.iter aux p
