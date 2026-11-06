(* Elaboration: name resolution (across IMPORTS), tagging (X.680 31),
   AUTOMATIC tagging (X.680 25.3), COMPONENTS OF, constraints, DEFAULT
   values, value references, and the `--#DEFINED-BY` tables of ANY DEFINED BY.
   Anonymous SEQUENCE, SET and CHOICE types are hoisted to named
   definitions, so that each of them gets a named C type. *)

open Ast

type id = { cls: tag_class; cons: bool; num: int }

(* A terminal: its F* `asn1_terminal_k` term and its F* impl type *)
type term = { tk: string; cty: string; ibound: string option (* INTEGER bound *) }

type node =                     (* an `asn1_k` *)
  | NRef of string              (* a named definition *)
  | NAny
  | NILC of id * cnode
and cnode =                     (* an `asn1_content_k` *)
  | CTerm of term * string option   (* with an optional F* asn1_restriction *)
  | CRef of string              (* the content of a named ILC definition *)
  | COf of bool * bool * node   (* SET?, nonempty?, item *)
  | CPrefixed of node           (* EXPLICIT tagging *)
  | CContaining of node         (* OCTET STRING (CONTAINING T): primitive *)

type fdeco =
  | FPlain
  | FOptional
  | FDefault of id * term * string option * string   (* id, terminal, restriction, F* literal *)

(* `fowner`: the name of the definition that owns the names generated for
   the component (its OPTIONAL/DEFAULT type, its DEFAULT value) *)
type field = { fname: string; fnode: node; fdeco: fdeco; fowner: string }

type alt =
  | ALeaf of string * id * cnode    (* name, identifier, content *)
  | ASub of string * string         (* name, a named CHOICE (flattened) *)

(* A SEQUENCE with an ANY DEFINED BY table: the components before the key
   (`prefix`), the key, then, for each supported key, the components after
   the key (`cases`), and those for the other keys (`fallback`, if any) *)
type adb_case = {
  cname: string;                    (* the name of the case *)
  clit: string;                     (* the F* key literal *)
  cfields: field list;
}

type adb = {
  prefix: field list;
  key: field;
  key_id: id;
  key_term: term;                   (* its `tk` may be an ASN1_PREFIXED_TERMINAL *)
  cases: adb_case list;
  fallback: field list option;
}

type def =
  | DStruct of bool * field list    (* SET?, components *)
  | DChoice of alt list
  | DNode of node
  | DAdb of adb

type env = {
  mname: string;                            (* the main ASN.1 module *)
  mutable td: tag_default;                  (* that of the current definition *)
  type_td: (string, tag_default) Hashtbl.t; (* that of the module of each type *)
  types: (string, typ) Hashtbl.t;           (* mangled name -> ASN.1 type *)
  values: (string, typ * value) Hashtbl.t;
  dbs: (string, defined_by) Hashtbl.t;      (* mangled type name -> its DEFINED-BY table *)
  lax_size_of: bool;                        (* SIZE on SEQUENCE OF / SET OF: only check lo >= 1 *)
  max_int_union: int;                       (* the maximal number of values of an INTEGER union *)
  defs: (string, def) Hashtbl.t;
  state: (string, bool) Hashtbl.t;          (* false: in progress *)
  mutable order: string list;               (* reverse topological order *)
  user: (string, string) Hashtbl.t;         (* mangled -> ASN.1 name *)
  keep: (string, unit) Hashtbl.t;           (* the KEEP-BYTES definitions *)
  keep_alias: (string, string) Hashtbl.t;   (* KEEP-BYTES retaggings: the C type of their values is that of the target *)
  keep_comps: (string, bool ref) Hashtbl.t; (* KEEP-BYTES components "T.c" (mangled), used? *)
}

let cls_name = function
  | Universal -> "UNIVERSAL" | Application -> "APPLICATION"
  | Context -> "CONTEXT_SPECIFIC" | Private -> "PRIVATE"

let idexpr (id: id) =
  match id.cls with
  | Universal ->
    if id.num = 0 then error "[UNIVERSAL 0] is not a valid tag";
    Printf.sprintf "(%s %d)" (if id.cons then "mk_constant_constructed_id" else "mk_constant_id") id.num
  | c -> Printf.sprintf "(mk_custom_id %s %s %d)" (cls_name c) (if id.cons then "CONSTRUCTED" else "PRIMITIVE") id.num

let mangle s = String.map (fun c -> if c = '-' then '_' else c) s

let univ ?(cons = false) num = { cls = Universal; cons; num }

let integer_term = { tk = "(ASN1_INTEGER asn1_any_integer_bound)"; cty = "asn1_int_impl"; ibound = Some "asn1_any_integer_bound" }
let small_integer_term = { tk = "(ASN1_INTEGER 8)"; cty = "I64.t"; ibound = Some "8" }
let slice = "(S.slice U8.t)"
let simple tk cty = { tk; cty; ibound = None }

let builtin (s: string) : id * term =
  let str n tk = univ n, simple tk slice in
  match s with
  | "BOOLEAN" -> univ 1, simple "ASN1_BOOLEAN" "bool"
  | "NULL" -> univ 5, simple "ASN1_NULL" "unit"
  | "OCTET STRING" -> str 4 "ASN1_OCTETSTRING"
  | "OBJECT IDENTIFIER" -> str 6 "ASN1_OID"
  | "ObjectDescriptor" -> str 7 "ASN1_OBJECTDESCRIPTOR"
  | "UTF8String" -> str 12 "ASN1_UTF8STRING"
  | "RELATIVE-OID" -> str 13 "ASN1_RELATIVE_OID"
  | "NumericString" -> str 18 "ASN1_NUMERICSTRING"
  | "PrintableString" -> str 19 "ASN1_PRINTABLESTRING"
  | "TeletexString" | "T61String" -> str 20 "ASN1_TELETEXSTRING"
  | "VideotexString" -> str 21 "ASN1_VIDEOTEXSTRING"
  | "IA5String" -> str 22 "ASN1_IA5STRING"
  | "UTCTime" -> str 23 "ASN1_UTCTIME"
  | "GeneralizedTime" -> str 24 "ASN1_GENERALIZEDTIME"
  | "GraphicString" -> str 25 "ASN1_GRAPHICSTRING"
  | "VisibleString" | "ISO646String" -> str 26 "ASN1_VISIBLESTRING"
  | "GeneralString" -> str 27 "ASN1_GENERALSTRING"
  | "UniversalString" -> str 28 "ASN1_UNIVERSALSTRING"
  | "BMPString" -> str 30 "ASN1_BMPSTRING"
  | "DATE" -> str 31 "ASN1_DATE"
  | "TIME-OF-DAY" -> str 32 "ASN1_TIME_OF_DAY"
  | "DATE-TIME" -> str 33 "ASN1_DATE_TIME"
  | "OID-IRI" -> str 35 "ASN1_OID_IRI"
  | "RELATIVE-OID-IRI" -> str 36 "ASN1_RELATIVE_OID_IRI"
  | _ -> error "unsupported type %s" s

let bitstring_term = simple "ASN1_BITSTRING" "asn1_bitstring_impl"

let def_of env n =
  match Hashtbl.find_opt env.defs n with
  | Some d -> d
  | None -> error "internal error: %s is not elaborated" n

(* Resolve a node to its ILC identifier and the content to use when
   retagging it (`CRef` keeps the sharing with the named definition) *)
type resolved = RILC of id * cnode | RChoice of string | RAny

let rec resolve env (n: node) : resolved =
  match n with
  | NAny -> RAny
  | NILC (id, c) -> RILC (id, c)
  | NRef r ->
    begin match def_of env r with
    | DStruct (set, _) -> RILC (univ ~cons:true (if set then 17 else 16), CRef r)
    | DAdb _ -> RILC (univ ~cons:true 16, CRef r)
    | DChoice _ -> RChoice r
    | DNode n' ->
      match resolve env n' with
      | RILC (id, _) -> RILC (id, CRef r)
      | x -> x
    end

(* The structural content behind `CRef`s *)
let rec struct_content env (c: cnode) : cnode =
  match c with
  | CRef r ->
    begin match resolve_struct env (NRef r) with
    | Some (_, c') -> c'
    | None -> error "internal error: %s is not an ILC" r
    end
  | _ -> c

and resolve_struct env n =
  match n with
  | NILC (id, c) -> Some (id, struct_content env c)
  | NRef r ->
    begin match def_of env r with
    | DNode n' -> resolve_struct env n'
    | DStruct _ | DAdb _ -> (match resolve env n with RILC (id, c) -> Some (id, c) | _ -> None)
    | DChoice _ -> None
    end
  | NAny -> None

let content_cons env c =
  match struct_content env c with
  | CTerm _ | CContaining _ -> false
  | CRef _ -> true (* a SEQUENCE or SET *)
  | COf _ | CPrefixed _ -> true

(* Named values of an INTEGER or ENUMERATED type *)
let enum_values items =
  let used = List.filter_map snd items in
  let rec next n = if List.mem n used then next (n + 1) else n in
  let _, l = List.fold_left (fun (cur, acc) (name, v) ->
      match v with
      | Some v -> (cur, (name, v) :: acc)
      | None -> let v = next cur in (v + 1, (name, v) :: acc))
      (0, []) items
  in
  List.rev l

let rec named_values env (t: typ) : (string * int) list =
  match t with
  | TInteger l -> l
  | TEnumerated items -> enum_values items
  | TRef r -> (match Hashtbl.find_opt env.types (mangle r) with Some t -> named_values env t | None -> [])
  | TTagged (_, _, _, t) | TConstrained (t, _) -> named_values env t
  | _ -> []

(* DER contents of an INTEGER (X.690 8.3): minimal two's complement *)
let int_bytes (v: int) : int list =
  let rec go v acc =
    let b = v land 0xff in
    let v' = v asr 8 in
    let acc = b :: acc in
    if (v' = 0 && b < 0x80) || (v' = -1 && b >= 0x80) then acc else go v' acc
  in go v []

let rec int_value env (src: typ) (v: value) : int =
  match v with
  | VInt i -> i
  | VName n ->
    begin match List.assoc_opt n (named_values env src) with
    | Some i -> i
    | None ->
      match Hashtbl.find_opt env.values n with
      | Some (t, v) -> int_value env t v
      | None -> error "unknown value %s" n
    end
  | _ -> error "expected an INTEGER value"

let rec bool_value env (v: value) : bool =
  match v with
  | VBool b -> b
  | VName n ->
    (match Hashtbl.find_opt env.values n with
     | Some (_, v) -> bool_value env v
     | None -> error "unknown value %s" n)
  | _ -> error "expected a BOOLEAN value"

(* The arcs of an OBJECT IDENTIFIER value *)
let rec oid_value ?(depth = 0) env (v: value) : int list =
  if depth > 100 then error "cyclic OBJECT IDENTIFIER values";
  let lookup s = match Hashtbl.find_opt env.values s with
    | Some (_, v) -> Some (oid_value ~depth:(depth + 1) env v)
    | None -> None
  in
  match v with
  | VName s -> (match lookup s with Some l -> l | None -> error "unknown value %s" s)
  | VOid comps ->
    let arc = function
      | ONum n | ONamed (_, n) -> n
      | OName s -> error "OBJECT IDENTIFIER component %s: write %s(n)" s s
    in
    let l = match comps with
      | OName s :: q ->
        let first = match lookup s, s with
          | Some l, _ -> l
          | None, ("itu-t" | "ccitt") -> [0]
          | None, "iso" -> [1]
          | None, ("joint-iso-itu-t" | "joint-iso-ccitt") -> [2]
          | None, _ -> error "unknown OBJECT IDENTIFIER value %s" s
        in
        first @ List.map arc q
      | _ -> List.map arc comps
    in
    if List.exists (fun n -> n < 0 || n >= 1 lsl 32) l then error "OBJECT IDENTIFIER arc out of range";
    l
  | _ -> error "expected an OBJECT IDENTIFIER value"

(* Follow the value references *)
let rec deref ?(depth = 0) env (v: value) : value =
  if depth > 100 then error "cyclic values";
  match v with
  | VName n ->
    (match Hashtbl.find_opt env.values n with
     | Some (_, v) -> deref ~depth:(depth + 1) env v
     | None -> error "unknown value %s" n)
  | _ -> v

let rec named_bits env (t: typ) : (string * int) list =
  match t with
  | TBitString l -> l
  | TRef r -> (match Hashtbl.find_opt env.types (mangle r) with Some t -> named_bits env t | None -> [])
  | TTagged (_, _, _, t) | TConstrained (t, _) -> named_bits env t
  | _ -> []

let hex_digit c = if c <= '9' then Char.code c - 48 else Char.code c - 55

(* The bits of a BIT STRING value (X.680 22.9, 22.16): with named bits,
   without its trailing 0 bits (X.690 11.2.2) *)
let bits_value env (src: typ) (v: value) : bool list =
  let named = named_bits env src in
  let bits = match deref env v with
    | VBString b -> List.init (String.length b) (fun i -> b.[i] = '1')
    | VHString h ->
      List.concat (List.init (String.length h) (fun i ->
          let d = hex_digit h.[i] in List.init 4 (fun j -> d land (8 lsr j) <> 0)))
    | VBits names ->
      let pos = List.map (fun n -> match List.assoc_opt n named with
          | Some i -> i
          | None -> error "unknown named bit %s" n) names in
      let len = List.fold_left (fun m i -> max m (i + 1)) 0 pos in
      List.init len (fun i -> List.mem i pos)
    | VOid [OName n] ->
      let i = match List.assoc_opt n named with Some i -> i | None -> error "unknown named bit %s" n in
      List.init (i + 1) (fun j -> j = i)
    | _ -> error "expected a BIT STRING value"
  in
  if named = [] then bits
  else
    let rec drop = function true :: _ as l -> l | false :: q -> drop q | [] -> [] in
    List.rev (drop (List.rev bits))

(* The bytes of bits, with the number of unused bits of the last byte *)
let bytes_of_bits (bits: bool list) : int * int list =
  let n = List.length bits in
  let nb = (n + 7) / 8 in
  let a = Array.of_list bits in
  let bytes = List.init nb (fun i ->
      let b = ref 0 in
      for j = 0 to 7 do
        let k = 8 * i + j in
        if k < n && a.(k) then b := !b lor (0x80 lsr j)
      done; !b)
  in
  (8 * nb - n, bytes)

(* The code points of a UTF-8 string *)
let code_points (s: string) : int list =
  let rec go i acc =
    if i >= String.length s then List.rev acc
    else
      let d = String.get_utf_8_uchar s i in
      if not (Uchar.utf_decode_is_valid d) then error "string \"%s\": invalid UTF-8" s;
      go (i + Uchar.utf_decode_length d) (Uchar.to_int (Uchar.utf_decode_uchar d) :: acc)
  in go 0 []

(* The code points of a character string value: a cstring, or a
   CharacterStringList of cstrings, value references, Quadruples
   {group, plane, row, cell} and Tuples {column, row} (X.680 41.8) *)
let rec char_value ?(depth = 0) env (v: value) : int list =
  if depth > 100 then error "cyclic values";
  let item = function
    | VNumList [g; p; r; c] ->
      if List.exists (fun x -> x < 0 || x > 255) [g; p; r; c] || g > 127 then error "bad Quadruple";
      [(g lsl 24) lor (p lsl 16) lor (r lsl 8) lor c]
    | VNumList [col; row] ->
      if col < 0 || col > 7 || row < 0 || row > 15 then error "bad Tuple";
      [col * 16 + row]
    | VNumList _ -> error "expected a Quadruple {g, p, r, c} or a Tuple {column, row}"
    | v -> char_value ~depth:(depth + 1) env v
  in
  match v with
  | VName n ->
    (match Hashtbl.find_opt env.values n with
     | Some (_, v) -> char_value ~depth:(depth + 1) env v
     | None -> error "unknown value %s" n)
  | VCString s -> code_points s
  | VCharList l -> List.concat_map item l
  | VBits names -> List.concat_map (fun n -> item (VName n)) names (* { ref1, ref2 } *)
  | _ -> error "expected a character string value \"...\""

let utf8_encode (cps: int list) : int list =
  let b = Buffer.create 16 in
  List.iter (fun c ->
      if not (Uchar.is_valid c) then error "U+%04X is not a Unicode scalar value" c;
      Buffer.add_utf_8_uchar b (Uchar.of_int c)) cps;
  List.init (Buffer.length b) (fun i -> Char.code (Buffer.nth b i))

(* The DER contents of a string value of a terminal: OCTET STRING from a
   bstring or hstring (X.680 22.10), character strings from a cstring or
   a CharacterStringList *)
let string_bytes env (tk: string) (v: value) : int list =
  let cps () = char_value env v in
  let check what ok =
    let l = cps () in
    List.iter (fun c -> if not (ok c) then error "character U+%04X is not allowed in %s" c what) l; l
  in
  let printable c =
    (c >= Char.code 'A' && c <= Char.code 'Z') || (c >= Char.code 'a' && c <= Char.code 'z') ||
    (c >= Char.code '0' && c <= Char.code '9') || String.contains " '()+,-./:=?" (Char.chr (c land 0x7f)) && c < 128
  in
  match tk with
  | "ASN1_OCTETSTRING" ->
    begin match deref env v with
      | VBString _ | VHString _ as v' ->
        let bits = match v' with
          | VBString b -> List.init (String.length b) (fun i -> b.[i] = '1')
          | VHString h -> List.concat (List.init (String.length h) (fun i ->
              let d = hex_digit h.[i] in List.init 4 (fun j -> d land (8 lsr j) <> 0)))
          | _ -> []
        in snd (bytes_of_bits bits)
      | _ -> error "expected an OCTET STRING value 'hex'H or 'bits'B"
    end
  | "ASN1_UTF8STRING" -> utf8_encode (cps ())
  | "ASN1_BMPSTRING" ->
    List.concat_map (fun c -> [c lsr 8; c land 0xff])
      (check "BMPString" (fun c -> c <= 0xffff && not (c >= 0xd800 && c <= 0xdfff)))
  | "ASN1_UNIVERSALSTRING" ->
    List.concat_map (fun c -> [c lsr 24; (c lsr 16) land 0xff; (c lsr 8) land 0xff; c land 0xff])
      (check "UniversalString" (fun c -> c <= 0x10ffff && not (c >= 0xd800 && c <= 0xdfff)))
  | "ASN1_PRINTABLESTRING" -> check "PrintableString" printable
  | "ASN1_NUMERICSTRING" -> check "NumericString" (fun c -> c = 32 || (c >= 48 && c <= 57))
  | "ASN1_VISIBLESTRING" -> check "VisibleString" (fun c -> c >= 32 && c <= 126)
  | "ASN1_IA5STRING" -> check "IA5String" (fun c -> c < 128)
  | "ASN1_TELETEXSTRING" | "ASN1_VIDEOTEXSTRING" | "ASN1_GRAPHICSTRING" | "ASN1_GENERALSTRING"
  | "ASN1_OBJECTDESCRIPTOR" ->
    check "this string type (only ASCII values are supported)" (fun c -> c >= 32 && c <= 126)
  | _ -> error "values of this type are not supported"

(* The DER contents of a value of a time type (X.680 38.4.1, 46, 47) or of
   an OID-IRI / RELATIVE-OID-IRI (X.680 34, 35); their validity is checked
   by F* (ASN1.Lit) *)
let time_bytes env (tk: string) (v: value) : int list =
  let s = match deref env v with
    | VCString s -> s
    | _ -> error "expected a string value \"...\""
  in
  let ascii s = List.init (String.length s) (fun i -> Char.code s.[i]) in
  let digits s = String.for_all (fun c -> c >= '0' && c <= '9') s in
  let fmt what f =
    match f s with
    | Some s' when digits s' -> ascii s'
    | _ -> error "expected a %s value" what
  in
  let date d =
    if String.length d = 10 && d.[4] = '-' && d.[7] = '-'
    then Some (String.sub d 0 4 ^ String.sub d 5 2 ^ String.sub d 8 2) else None
  in
  let tod t =
    if String.length t = 8 && t.[2] = ':' && t.[5] = ':'
    then Some (String.sub t 0 2 ^ String.sub t 3 2 ^ String.sub t 6 2) else None
  in
  match tk with
  | "ASN1_UTCTIME" ->
    if String.length s <> 13 || s.[12] <> 'Z' || not (digits (String.sub s 0 12)) then
      error "expected a DER UTCTime value \"YYMMDDhhmmssZ\"";
    ascii s
  | "ASN1_GENERALIZEDTIME" ->
    let n = String.length s in
    if n < 15 || s.[n - 1] <> 'Z' || not (digits (String.sub s 0 14)) ||
       (n > 15 && (s.[14] <> '.' || n = 16 || not (digits (String.sub s 15 (n - 16))) || s.[n - 2] = '0')) then
      error "expected a DER GeneralizedTime value \"YYYYMMDDhhmmss[.fff]Z\"";
    ascii s
  | "ASN1_DATE" -> fmt "DATE \"YYYY-MM-DD\"" date
  | "ASN1_TIME_OF_DAY" -> fmt "TIME-OF-DAY \"hh:mm:ss\"" tod
  | "ASN1_DATE_TIME" ->
    fmt "DATE-TIME \"YYYY-MM-DDThh:mm:ss\"" (fun s ->
        if String.length s = 19 && s.[10] = 'T' then
          match date (String.sub s 0 10), tod (String.sub s 11 8) with
          | Some d, Some t -> Some (d ^ t)
          | _ -> None
        else None)
  | "ASN1_OID_IRI" | "ASN1_RELATIVE_OID_IRI" -> ignore (code_points s); ascii s
  | _ -> error "values of this type are not supported"

(* The size of a string value (X.680 51.5): octets of an OCTET STRING and
   of the ISO 2022 string types, characters of the other ones *)
let value_size env (tk: string) (v: value) : int =
  match tk with
  | "ASN1_OCTETSTRING" | "ASN1_TELETEXSTRING" | "ASN1_VIDEOTEXSTRING" | "ASN1_GRAPHICSTRING"
  | "ASN1_GENERALSTRING" | "ASN1_OBJECTDESCRIPTOR" -> List.length (string_bytes env tk v)
  | _ -> ignore (string_bytes env tk v); List.length (char_value env v)

let bytes_lit (l: int list) =
  Printf.sprintf "[%s]" (String.concat "; " (List.map (Printf.sprintf "0x%02xuy") l))

(* Resolve the value references in the bounds of a constraint, and the
   excluded endpoints of ranges (lo<.. is lo+1.., ..<hi is ..hi-1) *)
let rec norm_constr env (c: constr) : constr =
  let rec b = function
    | BRef s ->
      (match deref env (VName s) with
       | VBool v -> BBool v
       | _ -> Val (int_value env (TInteger []) (VName s)))
    | Open x -> Open (b x)
    | x -> x
  in
  let opened d x = match b x with
    | Open (Val v) -> Val (v + d)
    | Open (Open _) -> error "bad range endpoint"
    | Open x | x -> x  (* MIN< and <MAX: unbounded anyway *)
  in
  match c with
  | CSize c -> CSize (norm_constr env c)
  | CRange (lo, hi) ->
    let lo = opened 1 lo and hi = opened (-1) hi in
    (match lo, hi with
     | Val l, Val h when l > h -> error "empty range %d..%d" l h
     | Max, _ | _, Min -> error "bad range"
     | _ -> ());
    CRange (lo, hi)
  | CSingle l -> CSingle (List.map b l)
  | CUnion l -> CUnion (List.map (norm_constr env) l)
  | CContaining _ | CWithComponent _ | CWithComponents _ | CTable _ -> c

(* A union of INTEGER ranges and values, as sorted disjoint intervals
   (None: unbounded) *)
let union_intervals (where: string) (es: constr list) : (int option * int option) list =
  let ivs = List.concat_map (function
      | CRange (lo, hi) ->
        let f = function Val v -> Some v | Min | Max -> None | _ -> error "%s: bad constraint" where in
        [(f lo, f hi)]
      | CSingle l -> List.map (function Val v -> (Some v, Some v) | _ -> error "%s: bad constraint" where) l
      | _ -> error "%s: unsupported constraint in a union" where)
      es
  in
  let cmp_lo a b = match a, b with
    | None, None -> 0 | None, _ -> -1 | _, None -> 1 | Some x, Some y -> compare x y in
  let ivs = List.sort (fun (a, _) (b, _) -> cmp_lo a b) ivs in
  let rec merge = function
    | (l1, h1) :: (l2, h2) :: q ->
      let adjacent = match h1, l2 with
        | None, _ | _, None -> true
        | Some h, Some l -> l <= h + 1
      in
      if adjacent then
        let h = match h1, h2 with None, _ | _, None -> None | Some a, Some b -> Some (max a b) in
        merge ((l1, h) :: q)
      else (l1, h1) :: merge ((l2, h2) :: q)
    | l -> l
  in
  merge ivs

(* The KEEP-BYTES definition whose bytes the values of `r` keep, if any *)
let rec keep_target env (r: string) : string option =
  if Hashtbl.mem env.keep r then Some r
  else match Hashtbl.find_opt env.defs r with
    | Some (DNode (NRef r')) -> keep_target env r'
    | _ -> None

(* The KEEP-BYTES definition that owns the C type of the values of `r` *)
let rec kept_owner env (r: string) : string =
  match Hashtbl.find_opt env.keep_alias r with
  | Some r' -> kept_owner env r'
  | None -> r

(* A fresh definition name, starting with `name` *)
let fresh env (name: string) : string =
  let rec go n = if Hashtbl.mem env.state n || Hashtbl.mem env.types n then go (n ^ "_") else n in
  go name

(* Add a KEEP-BYTES definition `name` for a node (its dependencies are
   already elaborated) *)
let hoist_keep env (name: string) (nd: node) : string =
  let name = fresh env name in
  Hashtbl.replace env.defs name (DNode nd);
  Hashtbl.replace env.state name true;
  env.order <- name :: env.order;
  Hashtbl.replace env.keep name ();
  name

(* The types under the outermost tags *)
let rec under_tags f = function
  | TTagged (c, n, m, t) -> TTagged (c, n, m, under_tags f t)
  | t -> f t

let fstar_int i = if i < 0 then Printf.sprintf "(%d)" i else string_of_int i

(* Check that a DEFAULT value satisfies the restriction `r` of its type,
   for a readable error (F* checks it too) *)
let check_restricted env (where: string) (tm: term) (r: string) (v: value) : unit =
  try
    match Scanf.sscanf_opt r "(RESTRICT_SIZE %d %s@)" (fun lo hi -> (lo, hi)) with
    | Some (lo, hi) ->
      let hi = Scanf.sscanf_opt hi "(Some %d)" (fun h -> h) in
      let n = value_size env tm.tk v in
      if n < lo || (match hi with Some h -> n > h | None -> false) then
        error "the value has size %d, out of its SIZE constraint" n
    | None ->
      if tm.tk = "ASN1_BOOLEAN" then begin
        let b = string_of_bool (bool_value env v) in
        if not (List.mem b (String.split_on_char ' ' (String.map (function '[' | ']' | ';' | '(' | ')' -> ' ' | c -> c) r))) then
          error "the value %s is not allowed by its constraint" b
      end
  with Error s -> error "%s: %s" where s

let rec elab_def env (name: string) : unit =
  match Hashtbl.find_opt env.state name with
  | Some true -> ()
  | Some false -> error "recursive type %s is not supported" name
  | None ->
    let t = match Hashtbl.find_opt env.types name with
      | Some t -> t
      | None -> error "undefined type %s" name
    in
    let td = env.td in
    (match Hashtbl.find_opt env.type_td name with Some td' -> env.td <- td' | None -> ());
    elab_named env name t;
    env.td <- td

and elab_named env name t =
  if Hashtbl.mem env.state name then error "name clash: %s is defined twice (hoisted anonymous types are named <Type>_<component>)" name;
  (* T ::= U (WITH COMPONENTS ...): T is the rewritten structure itself *)
  let t, td = match t with
    | TConstrained (t', ((CWithComponent _ | CWithComponents _) as c)) -> with_inner env name t' c
    | _ -> t, env.td
  in
  let saved = env.td in
  env.td <- td;
  Hashtbl.replace env.state name false;
  let d = match t, Hashtbl.find_opt env.dbs name with
    | TSequence cs, Some db -> DAdb (adb env name cs db)
    | _, Some db -> error "line %d: DEFINED-BY %s: not a SEQUENCE" db.db_line db.db_type
    | TSequence cs, None -> DStruct (false, fields env name cs)
    | TSet cs, None -> DStruct (true, fields env name cs)
    | TChoice alts, None -> DChoice (choice env name alts)
    | _, None -> DNode (node env (name ^ "_body") t)
  in
  env.td <- saved;
  Hashtbl.replace env.defs name d;
  Hashtbl.replace env.state name true;
  env.order <- name :: env.order

(* Inner subtyping (X.680 51.8): the type `t` constrained by WITH COMPONENT(S)
   `c`, as a new type (with the tagging environment of its definition). The
   tags of the components are those of `t` (X.680 25.3: AUTOMATIC tags are
   computed before the constraint), so they are made explicit. *)
and with_inner env (where: string) (t: typ) (c: constr) : typ * tag_default =
  let bad fmt = Printf.ksprintf (fun s -> error "%s: WITH COMPONENT%s: %s" where
                                    (match c with CWithComponents _ -> "S" | _ -> "") s) fmt in
  match t, c with
  | TRef r, _ ->
    let r = mangle r in
    let t' = match Hashtbl.find_opt env.types r with Some t' -> t' | None -> error "undefined type %s" r in
    if Hashtbl.mem env.dbs r then bad "%s has a DEFINED-BY table: not supported" r;
    let saved = env.td in
    (match Hashtbl.find_opt env.type_td r with Some td -> env.td <- td | None -> ());
    let res = try with_inner env where t' c with e -> env.td <- saved; raise e in
    env.td <- saved;
    res
  | TTagged (cls, n, m, t'), _ ->
    let m = match m with TDefault -> if env.td = DExplicit then TExplicit else TImplicit | m -> m in
    let t'', td = with_inner env where t' c in
    TTagged (cls, n, m, t''), td
  | TConstrained (t', ((CWithComponent _ | CWithComponents _) as c0)), _ ->
    let t'', td = with_inner env where t' c0 in
    let saved = env.td in
    env.td <- td;
    let res = try with_inner env where t'' c with e -> env.td <- saved; raise e in
    env.td <- saved;
    res
  | (TSequenceOf (sz, elt) | TSetOf (sz, elt)), CWithComponent k ->
    let elt = under_tags (fun x -> TConstrained (x, k)) elt in
    (match t with TSetOf _ -> TSetOf (sz, elt) | _ -> TSequenceOf (sz, elt)), env.td
  | (TSequence cs | TSet cs), CWithComponents (partial, specs) ->
    let comps = tagged_components env where cs in
    List.iter (fun (n, _, _) ->
        if not (List.exists (fun (m, _, _, _) -> m = n) comps) then bad "no component %s" n)
      specs;
    let cs' = List.filter_map (fun (n, _, d, t) ->
        let spec = List.find_opt (fun (m, _, _) -> m = n) specs in
        let t = match spec with
          | Some (_, Some k, _) -> under_tags (fun x -> TConstrained (x, k)) t
          | _ -> t
        in
        let pres = match spec with
          | Some (_, _, p) -> p
          | None -> if partial || d <> DOptional then None else Some PAbsent  (* X.680 51.8.6 *)
        in
        match d, pres with
        | _, None -> Some (Field (n, t, d))
        | DOptional, Some POptional -> Some (Field (n, t, d))
        | DOptional, Some PAbsent -> None
        | (DOptional | DPlain), Some PPresent -> Some (Field (n, t, DPlain))
        | DPlain, Some (PAbsent | POptional) -> bad "%s is not OPTIONAL" n
        | DDefault _, Some _ -> bad "presence constraints on the DEFAULT component %s are not supported" n)
        comps
    in
    (match t with TSet _ -> TSet cs' | _ -> TSequence cs'), env.td
  | TChoice alts, CWithComponents (partial, specs) ->
    let alts = auto_tag env alts alts in
    List.iter (fun (n, _, _) -> if not (List.mem_assoc n alts) then bad "no alternative %s" n) specs;
    let present = List.filter (fun (_, _, p) -> p = Some PPresent) specs in
    if List.length present > 1 then bad "at most one alternative may be PRESENT";
    let alts' = List.filter_map (fun (n, t) ->
        let spec = List.find_opt (fun (m, _, _) -> m = n) specs in
        let keep = match spec with
          | None -> partial && present = []
          | Some (_, _, Some PAbsent) -> false
          | Some (_, _, Some PPresent) -> true
          | Some (_, _, (Some POptional | None)) -> present = []
        in
        if not keep then None else
        let t = match spec with
          | Some (_, Some k, _) -> under_tags (fun x -> TConstrained (x, k)) t
          | _ -> t
        in
        Some (n, t))
        alts
    in
    if alts' = [] then bad "no alternative remains";
    TChoice alts', env.td
  | (TSequence _ | TSet _ | TChoice _), CWithComponent _ -> bad "on a SEQUENCE, SET or CHOICE: write WITH COMPONENTS"
  | (TSequenceOf _ | TSetOf _), CWithComponents _ -> bad "on a SEQUENCE OF or SET OF: write WITH COMPONENT"
  | _ -> bad "only on SEQUENCE, SET, CHOICE, SEQUENCE OF and SET OF types"

(* Elaborate a type into a node; anonymous constructed types are hoisted
   under the name `ctx` *)
and node env (ctx: string) (t: typ) : node =
  match t with
  | TSequence _ | TSet _ | TChoice _ ->
    if Hashtbl.mem env.types ctx then error "name clash: anonymous type %s" ctx;
    elab_named env ctx t; NRef ctx
  | TRef r -> let r = mangle r in elab_def env r; NRef r
  | TInst (n, _) -> error "%s: unexpanded instance of %s" ctx n
  | TField (c, f) -> error "%s: %s.&%s is supported only in the components of a SEQUENCE type assignment" ctx c f
  | TBuiltin s -> let id, tm = builtin s in NILC (id, CTerm (tm, None))
  | TInteger _ -> NILC (univ 2, CTerm (integer_term, None))
  | TEnumerated items ->
    let vs = List.map snd (enum_values items) in
    NILC (univ 10, CTerm (small_integer_term,
      Some (Printf.sprintf "(RESTRICT_INT_IN [%s])" (String.concat "; " (List.map fstar_int vs)))))
  | TBitString _ -> NILC (univ 3, CTerm (bitstring_term, None))
  | TAny -> NAny
  | TAnyDefinedBy _ -> NAny (* with no DEFINED-BY table *)
  | TSequenceOf (c, t') | TSetOf (c, t') ->
    let set = (match t with TSetOf _ -> true | _ -> false) in
    let c = Option.map (norm_constr env) c in
    let ne = match c with
      | None -> false
      | Some (CSize (CRange (Val 1, Max))) -> true
      | Some (CSize (CRange (Val 0, Max))) -> false
      | Some (CSize (CRange (Val lo, _) | CSingle [Val lo])) when env.lax_size_of && lo >= 0 -> lo >= 1
      | Some (CSize (CRange (Min, _))) when env.lax_size_of -> false
      | Some _ -> error "%s: only SIZE (1..MAX) is supported on SEQUENCE OF / SET OF (or, with --lax_size_of, SIZE (lo..hi), checking only lo >= 1)" ctx
    in
    NILC (univ ~cons:true (if set then 17 else 16), COf (set, ne, node env (ctx ^ "_elt") t'))
  | TTagged (cls, num, mode, t') ->
    let inner = node env ctx t' in
    let implicit = match mode with
      | TImplicit -> true
      | TExplicit -> false
      | TDefault -> env.td <> DExplicit
    in
    begin match resolve env inner with
    | RILC (_, c) when implicit ->
      let nd = NILC ({ cls; num; cons = content_cons env c }, c) in
      begin match c with
        | CRef r ->
          (* IMPLICIT tagging reuses the content of r: keep the bytes in a
             new KEEP-BYTES definition, with the C type of r *)
          begin match keep_target env r with
            | Some t ->
              let a = hoist_keep env (ctx ^ "_kept") nd in
              Hashtbl.replace env.keep_alias a t;
              NRef a
            | None -> nd
          end
        | _ -> nd
      end
    | _ -> NILC ({ cls; num; cons = true }, CPrefixed inner)  (* X.680 31.2.7 *)
    end
  | TConstrained (t', ((CWithComponent _ | CWithComponents _) as c)) ->
    let t'', td = with_inner env ctx t' c in
    let saved = env.td in
    env.td <- td;
    let res = try node env ctx t'' with e -> env.td <- saved; raise e in
    env.td <- saved;
    res
  | TConstrained (t', CContaining t'') ->
    let inner = node env ctx t' in
    begin match resolve_struct env inner with
    | Some (id, CTerm ({ tk = "ASN1_OCTETSTRING"; _ }, None)) ->
      NILC (id, CContaining (node env (ctx ^ "_contents") t''))
    | _ -> error "%s: CONTAINING is supported on OCTET STRING only" ctx
    end
  | TConstrained (t', c) ->
    let c = norm_constr env c in
    let inner = node env ctx t' in
    begin match resolve_struct env inner, c with
    | Some (id, CTerm (tm, None)), _ when tm.ibound <> None ->
      begin match c with
      | CRange (Val lo, Val hi) ->
        NILC (id, CTerm (small_integer_term, Some (Printf.sprintf "(RESTRICT_INT_RANGE (Some %s) (Some %s))" (fstar_int lo) (fstar_int hi))))
      | CRange (lo, hi) ->
        let b = function Val v -> Printf.sprintf "(Some %s)" (fstar_int v) | _ -> "None" in
        NILC (id, CTerm (integer_term, Some (Printf.sprintf "(RESTRICT_INT_RANGE %s %s)" (b lo) (b hi))))
      | CSingle vs ->
        let vs = List.map (function Val v -> v | _ -> error "%s: bad constraint" ctx) vs in
        NILC (id, CTerm (small_integer_term, Some (Printf.sprintf "(RESTRICT_INT_IN [%s])" (String.concat "; " (List.map fstar_int vs)))))
      | CUnion es ->
        begin match union_intervals ctx es with
        | [(lo, hi)] ->
          let b = function Some v -> Printf.sprintf "(Some %s)" (fstar_int v) | None -> "None" in
          let tm = if lo <> None && hi <> None then small_integer_term else integer_term in
          NILC (id, CTerm (tm, Some (Printf.sprintf "(RESTRICT_INT_RANGE %s %s)" (b lo) (b hi))))
        | ivs ->
          let max_values = env.max_int_union in
          let vs = List.concat_map (function
              | Some lo, Some hi when hi - lo < max_values -> List.init (hi - lo + 1) (fun i -> lo + i)
              | _ -> error "%s: a union of ranges must be a single range, or have at most %d values" ctx max_values)
              ivs
          in
          if List.length vs > max_values then
            error "%s: a union of ranges must be a single range, or have at most %d values" ctx max_values;
          NILC (id, CTerm (small_integer_term, Some (Printf.sprintf "(RESTRICT_INT_IN [%s])" (String.concat "; " (List.map fstar_int vs)))))
        end
      | CSize _ | CContaining _ | CWithComponent _ | CWithComponents _ | CTable _ -> error "%s: unsupported constraint on INTEGER" ctx
      end
    | Some (id, CTerm ({ tk = "ASN1_BOOLEAN"; _ } as tm, None)), CSingle bs ->
      let vs = List.sort_uniq compare (List.map (function
          | BBool b -> b
          | _ -> error "%s: expected TRUE or FALSE" ctx) bs) in
      NILC (id, CTerm (tm, Some (Printf.sprintf "(RESTRICT_IN [%s])" (String.concat "; " (List.map string_of_bool vs)))))
    | Some (id, CTerm ({ tk = ("ASN1_OCTETSTRING" | "ASN1_UTF8STRING" | "ASN1_BMPSTRING"
                             | "ASN1_UNIVERSALSTRING" | "ASN1_PRINTABLESTRING" | "ASN1_IA5STRING"
                             | "ASN1_VISIBLESTRING" | "ASN1_NUMERICSTRING" | "ASN1_TELETEXSTRING"
                             | "ASN1_VIDEOTEXSTRING" | "ASN1_GRAPHICSTRING" | "ASN1_GENERALSTRING"
                             | "ASN1_OBJECTDESCRIPTOR"); _ } as tm, None)), CSize sz ->
      let sz = match sz with
        | CUnion es ->
          begin match union_intervals ctx es with
            | [(lo, hi)] ->
              CRange ((match lo with Some v -> Val v | None -> Min), (match hi with Some v -> Val v | None -> Max))
            | _ -> error "%s: a SIZE union must be a single range" ctx
          end
        | _ -> sz
      in
      let lo, hi = match sz with
        | CRange (Val lo, Max) when lo >= 0 -> lo, "None"
        | CRange (Val lo, Val hi) when lo >= 0 -> lo, Printf.sprintf "(Some %d)" hi
        | CRange (Min, Val hi) -> 0, Printf.sprintf "(Some %d)" hi
        | CSingle [Val n] when n >= 0 -> n, Printf.sprintf "(Some %d)" n
        | _ -> error "%s: unsupported SIZE constraint" ctx
      in
      NILC (id, CTerm (tm, Some (Printf.sprintf "(RESTRICT_SIZE %d %s)" lo hi)))
    | _ -> error "%s: constraints are supported on INTEGER, BOOLEAN and on the SIZE of OCTET STRING and character strings only" ctx
    end

and components env (name: string) (cs: component list) : (string * typ * deco) list =
  List.concat_map (function
      | Field (n, t, d) -> [(n, t, d)]
      | ComponentsOf (TRef r) ->
        begin match Hashtbl.find_opt env.types (mangle r) with
        | Some (TSequence cs') | Some (TSet cs') -> components env name cs'
        | _ -> error "%s: COMPONENTS OF %s: not a SEQUENCE or SET" name r
        end
      | ComponentsOf _ -> error "%s: COMPONENTS OF must name a type" name)
    cs

(* X.680 25.3: AUTOMATIC tagging when no component is tagged *)
and auto_tag env (own: (string * typ) list) (all: (string * typ) list) : (string * typ) list =
  let tagged = function TTagged _ -> true | _ -> false in
  if env.td = DAutomatic && not (List.exists (fun (_, t) -> tagged t) own)
  then List.mapi (fun i (n, t) -> (n, TTagged (Context, i, TImplicit, t))) all
  else all

(* The components (name, declared type, decoration, tagged type) *)
and tagged_components env name cs : (string * typ * deco * typ) list =
  let own = List.filter_map (function Field (n, t, _) -> Some (n, t) | _ -> None) cs in
  let all = components env name cs in
  let tagged = auto_tag env own (List.map (fun (n, t, _) -> (n, t)) all) in
  let seen = Hashtbl.create 7 in
  List.map2 (fun (n, src, d) (_, t) ->
      if Hashtbl.mem seen (mangle n) then error "%s: duplicate component %s" name n;
      Hashtbl.add seen (mangle n) ();
      (n, src, d, t))
    all tagged

(* The terminal of a component, for DEFAULT values and ANY DEFINED BY keys:
   its identifier, its terminal, its restriction, and the terminal of
   its literals (without the EXPLICIT tag, if any) *)
and terminal_of env (fnode: node) : (id * term * string option * term) option =
  match resolve_struct env fnode with
  | Some (id, CTerm (tm, r)) -> Some (id, tm, r, tm)
  | Some (id, CPrefixed inner) ->
    begin match resolve_struct env inner with
    | Some (iid, CTerm (tm, None)) ->
      Some (id, { tm with tk = Printf.sprintf "(ASN1_PREFIXED_TERMINAL %s %s)" (idexpr iid) tm.tk }, None, tm)
    | _ -> None
    end
  | _ -> None

(* The F* literal of a value of a terminal *)
and literal env (where: string) (src: typ) (tm: term) (v: value) : string =
  try
    match tm.tk, tm.ibound with
    | "ASN1_BOOLEAN", _ -> string_of_bool (bool_value env v)
    | "ASN1_NULL", _ -> (match deref env v with VNull -> "()" | _ -> error "expected NULL")
    | "ASN1_OID", _ ->
      Printf.sprintf "(mk_oid [%s])" (String.concat "; " (List.map string_of_int (oid_value env v)))
    | "ASN1_BITSTRING", _ ->
      let unused, bytes = bytes_of_bits (bits_value env src v) in
      (* proved by normalization (ASN1.Lit): SMT may time out *)
      let l = bytes_lit bytes in
      Printf.sprintf "(let l : list FStar.UInt8.t = %s in assert_norm (ASN1.Lit.bitstring_l %duy %s); ASN1.Lit.bitstring_l_correct %duy l; (%duy, l))" l unused l unused unused
    | "ASN1_RELATIVE_OID", _ -> error "values of this type are not supported"
    | ("ASN1_UTCTIME" | "ASN1_GENERALIZEDTIME" | "ASN1_DATE" | "ASN1_TIME_OF_DAY"
      | "ASN1_DATE_TIME" | "ASN1_OID_IRI" | "ASN1_RELATIVE_OID_IRI" as tk), _ ->
      let p = match tk with
        | "ASN1_UTCTIME" -> "utctime" | "ASN1_GENERALIZEDTIME" -> "gentime" | "ASN1_DATE" -> "date"
        | "ASN1_TIME_OF_DAY" -> "tod" | "ASN1_DATE_TIME" -> "datetime" | "ASN1_OID_IRI" -> "oid_iri"
        | _ -> "rel_oid_iri"
      in
      let l = bytes_lit (time_bytes env tk v) in
      Printf.sprintf "(let l : list FStar.UInt8.t = %s in assert_norm (ASN1.Lit.%s_l %s); ASN1.Lit.%s_lit l ())" l p l p
    | _, Some b ->
      let bytes = int_bytes (int_value env src v) in
      Printf.sprintf "(mk_int_lit %s [%s] ())" b
        (String.concat "; " (List.map (Printf.sprintf "%duy") bytes))
    | tk, None ->
      let l = bytes_lit (string_bytes env tk v) in
      let pred = match tk with
        | "ASN1_UTF8STRING" -> Some ("utf8_l", "utf8_l_correct l")
        | "ASN1_BMPSTRING" -> Some ("bmp_l", "bmp_l_correct l 0")
        | "ASN1_UNIVERSALSTRING" -> Some ("universal_l", "universal_l_correct l 0")
        | _ -> None
      in
      begin match pred with
        | Some (p, lem) ->
          Printf.sprintf "(let l : list FStar.UInt8.t = %s in assert_norm (ASN1.Lit.%s %s); ASN1.Lit.%s; l)" l p l lem
        | None -> l
      end
  with Error s -> error "%s: %s" where s

and elab_field ?(keep_ok = true) env owner ((n, src, d, t): string * typ * deco * typ) : field =
  let fname = mangle n in
  let fnode = node env (owner ^ "_" ^ fname) t in
  let fnode = match Hashtbl.find_opt env.keep_comps (owner ^ "." ^ fname) with
    | None -> fnode
    | Some used ->
      used := true;
      if not keep_ok then error "%s.%s: KEEP-BYTES is not supported on the key or the dependent component of a DEFINED-BY table" owner n;
      (match d with DDefault _ -> error "%s.%s: KEEP-BYTES is not supported on DEFAULT components" owner n | _ -> ());
      begin match fnode with
        | NRef r when r = owner ^ "_" ^ fname && not (Hashtbl.mem env.types r) ->
          (* an anonymous type, hoisted for this component *)
          Hashtbl.replace env.keep r (); fnode
        | _ -> NRef (hoist_keep env (owner ^ "_" ^ fname) fnode)
      end
  in
  let fdeco = match d with
    | DPlain -> FPlain
    | DOptional -> FOptional
    | DDefault v ->
      let where = Printf.sprintf "%s.%s: DEFAULT" owner n in
      begin match terminal_of env fnode with
      | Some (id, tm, r, ltm) ->
        let lit = literal env where src ltm v in
        (match r with Some r -> check_restricted env where ltm r v | None -> ());
        FDefault (id, tm, r, lit)
      | None -> error "%s: supported on simple types only (possibly EXPLICIT-tagged, unconstrained)" where
      end
  in
  { fname; fnode; fdeco; fowner = owner }

and fields env name cs : field list =
  List.map (elab_field env name) (tagged_components env name cs)

(* A SEQUENCE with a DEFINED-BY table *)
and adb env name cs (db: defined_by) : adb =
  let where = Printf.sprintf "line %d: DEFINED-BY %s.%s" db.db_line db.db_type db.db_field in
  let comps = tagged_components env name cs in
  let index f =
    let rec go i = function
      | [] -> error "%s: %s has no component %s" where name f
      | (n, _, _, _) :: q -> if n = f then i else go (i + 1) q
    in go 0 comps
  in
  let dep_i = index db.db_field in
  let (dep_n, dep_src, _, dep_t) as dep = List.nth comps dep_i in
  let key_n = match db.db_key with
    | Some k -> k
    | None ->
      let k = ref None in
      ignore (under_tags (fun t -> (match t with TAnyDefinedBy x -> k := Some x | _ -> ()); t) dep_t);
      match !k with Some x -> x | None -> error "%s: not an ANY DEFINED BY: write BY <key component>" where
  in
  let key_i = index key_n in
  if key_i >= dep_i then error "%s: the key component %s must precede %s" where key_n db.db_field;
  let prefix = List.filteri (fun i _ -> i < key_i) comps in
  let (_, key_src, key_d, _) as key_c = List.nth comps key_i in
  if key_d <> DPlain then error "%s: the key component %s must not be OPTIONAL or DEFAULT" where key_n;
  let prefix = List.map (elab_field env name) prefix in
  let key = elab_field ~keep_ok:false env name key_c in
  let key_id, key_term, ltm = match terminal_of env key.fnode with
    | Some (id, tm, None, ltm) -> id, tm, ltm
    | Some (_, _, Some _, _) -> error "%s: the key component %s must not be constrained" where key_n
    | None -> error "%s: the key component %s must have a simple type" where key_n
  in
  (* The components after the key, other than the dependent one, are shared *)
  let after = List.filteri (fun i _ -> i > key_i) comps in
  let shared = List.map (fun ((n, _, _, _) as c) -> if n = dep_n then None else Some (elab_field env name c)) after in
  let with_dep owner (b: case_body option) : field list =
    let dep_field = match b with
      | None -> Some (elab_field ~keep_ok:false env name dep)
      | Some BAbsent -> None
      | Some (BType (t, opt)) ->
        Some (elab_field ~keep_ok:false env owner (dep_n, t, (if opt then DOptional else DPlain), under_tags (fun _ -> t) dep_t))
      | Some (BContaining t) ->
        Some (elab_field ~keep_ok:false env owner (dep_n, dep_src, DPlain, under_tags (fun d -> TConstrained (d, CContaining t)) dep_t))
    in
    List.filter_map (fun x -> x) (List.map (function Some f -> Some f | None -> dep_field) shared)
  in
  let seen = Hashtbl.create 7 in
  let cases = List.mapi (fun i (v, b) ->
      let cname = match v with
        | VName s -> mangle s
        | VBool b -> string_of_bool b
        | _ -> Printf.sprintf "k%d" i
      in
      if Hashtbl.mem seen cname || cname = "other" then error "%s: duplicate case %s" where cname;
      Hashtbl.add seen cname ();
      let clit = literal env where key_src ltm v in
      { cname; clit; cfields = with_dep (name ^ "_" ^ cname) (Some b) })
      db.db_cases
  in
  let fallback = match db.db_fallback with
    | FbNone -> None
    | FbDeclared -> Some (with_dep name None)
    | FbBody b -> Some (with_dep (name ^ "_other") (Some b))
  in
  if cases = [] && fallback = None then error "%s: no case and no fallback" where;
  { prefix; key; key_id; key_term; cases; fallback }

and choice env name alts : alt list =
  let alts = auto_tag env alts alts in
  let seen = Hashtbl.create 7 in
  List.map (fun (n, t) ->
      let n' = mangle n in
      if Hashtbl.mem seen n' then error "%s: duplicate alternative %s" name n;
      Hashtbl.add seen n' ();
      let nd = node env (name ^ "_" ^ n') t in
      match nd, resolve env nd with
      | NILC (id, c), _ -> ALeaf (n', id, c)
      | _, RILC (id, c) -> ALeaf (n', id, c)
      | _, RChoice r -> ASub (n', r)
      | _, RAny -> error "%s.%s: ANY is not supported as a CHOICE alternative" name n)
    alts

let rec refs (t: typ) : string list =
  match t with
  | TRef r -> [mangle r]
  | TSequence cs | TSet cs ->
    List.concat_map (function Field (_, t, _) -> refs t | ComponentsOf t -> refs t) cs
  | TChoice alts -> List.concat_map (fun (_, t) -> refs t) alts
  | TSequenceOf (_, t) | TSetOf (_, t) | TTagged (_, _, _, t) -> refs t
  | TConstrained (t, c) -> refs t @ constr_refs c
  | _ -> []

and constr_refs (c: constr) : string list =
  match c with
  | CContaining t -> refs t
  | CSize c | CWithComponent c -> constr_refs c
  | CUnion l -> List.concat_map constr_refs l
  | CWithComponents (_, l) -> List.concat_map (fun (_, c, _) -> match c with Some c -> constr_refs c | None -> []) l
  | CTable _ | CRange _ | CSingle _ -> []

let body_refs = function
  | BAbsent -> []
  | BType (t, _) | BContaining t -> refs t

(* Parameterized types (X.683): each instance `Name { args }` becomes an
   ordinary type assignment `Name_<args>` of the module of `Name` (so that
   it is tagged as there), memoized by its arguments *)
let expand_params (ms: modul list) : modul list =
  let templates = Hashtbl.create 7 in
  List.iter (fun (m: modul) ->
      List.iter (function
          | TypeTemplate (n, ps, t) ->
            if Hashtbl.mem templates n then error "parameterized type %s defined twice" n;
            Hashtbl.replace templates n (m.mname, ps, t)
          | _ -> ())
        m.assignments)
    ms;
  let taken = Hashtbl.create 17 in
  List.iter (fun (m: modul) ->
      List.iter (function
          | TypeAssign (n, _) | TypeTemplate (n, _, _) -> Hashtbl.replace taken (mangle n) ()
          | _ -> ())
        m.assignments)
    ms;
  let instances = Hashtbl.create 7 in            (* (name, args) -> instance name *)
  let extra = Hashtbl.create 7 in                (* module -> instances, in reverse order *)
  let rec arg_name = function
    | AType (TRef r) -> mangle r
    | AType (TInst (n, args)) -> String.concat "_" (mangle n :: List.map arg_name args)
    | AType (TBuiltin b) -> String.map (fun c -> if c = ' ' || c = '-' then '_' else c) b
    | AType (TInteger _) -> "INTEGER"
    | AType (TTagged (_, n, _, t)) -> Printf.sprintf "%d_%s" n (arg_name (AType t))
    | AValue (VInt i) -> if i < 0 then Printf.sprintf "m%d" (-i) else string_of_int i
    | AValue (VName s) -> mangle s
    | AValue (VBool b) -> string_of_bool b
    | ASet { elems = [ESet n]; _ } -> mangle n
    | _ -> "x"
  in
  let rec typ depth (t: typ) : typ =
    let go = typ depth in
    match t with
    | TRef r when Hashtbl.mem templates r -> error "parameterized type %s used without arguments" r
    | TInst (n, args) -> TRef (instance depth n (List.map (arg depth) args))
    | TSequence cs -> TSequence (List.map (comp depth) cs)
    | TSet cs -> TSet (List.map (comp depth) cs)
    | TSequenceOf (c, t) -> TSequenceOf (Option.map (constr depth) c, go t)
    | TSetOf (c, t) -> TSetOf (Option.map (constr depth) c, go t)
    | TChoice alts -> TChoice (List.map (fun (n, t) -> (n, go t)) alts)
    | TTagged (c, n, m, t) -> TTagged (c, n, m, go t)
    | TConstrained (t, c) -> TConstrained (go t, constr depth c)
    | TBuiltin _ | TInteger _ | TEnumerated _ | TBitString _ | TAny | TAnyDefinedBy _ | TRef _ | TField _ -> t
  and comp depth = function
    | Field (n, t, d) -> Field (n, typ depth t, d)
    | ComponentsOf t -> ComponentsOf (typ depth t)
  and constr depth (c: constr) : constr =
    match c with
    | CSize c -> CSize (constr depth c)
    | CUnion l -> CUnion (List.map (constr depth) l)
    | CContaining t -> CContaining (typ depth t)
    | CWithComponent c -> CWithComponent (constr depth c)
    | CWithComponents (p, l) -> CWithComponents (p, List.map (fun (n, c, pr) -> (n, Option.map (constr depth) c, pr)) l)
    | CRange _ | CSingle _ | CTable _ -> c
  and arg depth = function
    | AType t -> AType (typ depth t)
    | a -> a
  and instance depth n args =
    if depth > 100 then error "%s: too many nested instances (recursive parameterized types are not supported)" n;
    match Hashtbl.find_opt instances (n, args) with
    | Some i -> i
    | None ->
      let mname, ps, body = match Hashtbl.find_opt templates n with
        | Some x -> x
        | None -> error "%s is not a parameterized type" n
      in
      if List.length ps <> List.length args then
        error "%s: %d parameters expected, %d given" n (List.length ps) (List.length args);
      let base = String.concat "_" (mangle n :: List.map arg_name args) in
      let rec fresh i = let c = if i = 0 then base else Printf.sprintf "%s_%d" base i in
        if Hashtbl.mem taken c then fresh (i + 1) else c in
      let iname = fresh 0 in
      Hashtbl.replace taken iname ();
      Hashtbl.replace instances (n, args) iname;
      let tsub = List.concat (List.map2 (fun p a -> match p, a with
          | PType x, AType t -> [(x, t)]
          | PType x, AValue _ -> error "%s: the argument for %s must be a type" n x
          | PType x, ASet _ -> error "%s: the argument for %s must be a type" n x
          | (PValue _ | PSet _), _ -> []) ps args) in
      let vsub = List.concat (List.map2 (fun p a -> match p, a with
          | PValue (_, x), AValue v -> [(x, v)]
          | PValue (_, x), (AType _ | ASet _) -> error "%s: the argument for %s must be a value" n x
          | (PType _ | PSet _), _ -> []) ps args) in
      let ssub = List.concat (List.map2 (fun p a -> match p, a with
          | PSet (_, x), ASet o -> [(x, o)]
          | PSet (_, x), _ -> error "%s: the argument for %s must be an object set {...}" n x
          | (PType _ | PValue _), _ -> []) ps args) in
      let body = subst tsub vsub ssub body in
      let body = typ (depth + 1) body in
      let l = match Hashtbl.find_opt extra mname with Some l -> l | None -> [] in
      Hashtbl.replace extra mname (TypeAssign (iname, body) :: l);
      iname
  (* Substitute the formal parameters of a template (before expanding its instances) *)
  and subst tsub vsub ssub (t: typ) : typ =
    let go = subst tsub vsub ssub in
    let v = function
      | VName x when List.mem_assoc x vsub -> List.assoc x vsub
      | v -> v
    in
    let rec b = function
      | BRef x when List.mem_assoc x vsub ->
        (match List.assoc x vsub with
         | VInt i -> Val i
         | VBool bb -> BBool bb
         | VName y -> BRef y
         | _ -> error "the value parameter %s is used as a bound: expected an INTEGER or BOOLEAN" x)
      | Open x -> Open (b x)
      | x -> x
    in
    let rec c = function
      | CSize k -> CSize (c k)
      | CRange (lo, hi) -> CRange (b lo, b hi)
      | CSingle l -> CSingle (List.map b l)
      | CUnion l -> CUnion (List.map c l)
      | CContaining t -> CContaining (go t)
      | CWithComponent k -> CWithComponent (c k)
      | CWithComponents (p, l) -> CWithComponents (p, List.map (fun (n, k, pr) -> (n, Option.map c k, pr)) l)
      | CTable (o, k) -> CTable (set o, k)
    and set (o: obj_set) : obj_set =
      List.fold_left (fun (acc: obj_set) e -> match e with
          | ESet x when List.mem_assoc x ssub ->
            let o' = List.assoc x ssub in
            { elems = acc.elems @ o'.elems; ext = acc.ext || o'.ext }
          | e -> { acc with elems = acc.elems @ [e] })
        { elems = []; ext = o.ext } o.elems
    in
    let d = function DDefault x -> DDefault (v x) | d -> d in
    match t with
    | TRef r when List.mem_assoc r tsub -> List.assoc r tsub
    | TField (r, f) when List.mem_assoc r tsub ->
      (match List.assoc r tsub with
       | TRef r' -> TField (r', f)
       | _ -> error "the class parameter %s must be given a class" r)
    | TInst (n, args) -> TInst (n, List.map (function AType t -> AType (go t) | AValue x -> AValue (v x) | ASet o -> ASet (set o)) args)
    | TSequence cs -> TSequence (List.map (function Field (n, t, dd) -> Field (n, go t, d dd) | ComponentsOf t -> ComponentsOf (go t)) cs)
    | TSet cs -> TSet (List.map (function Field (n, t, dd) -> Field (n, go t, d dd) | ComponentsOf t -> ComponentsOf (go t)) cs)
    | TSequenceOf (k, t) -> TSequenceOf (Option.map c k, go t)
    | TSetOf (k, t) -> TSetOf (Option.map c k, go t)
    | TChoice alts -> TChoice (List.map (fun (n, t) -> (n, go t)) alts)
    | TTagged (cl, n, m, t) -> TTagged (cl, n, m, go t)
    | TConstrained (t, k) -> TConstrained (go t, c k)
    | TBuiltin _ | TInteger _ | TEnumerated _ | TBitString _ | TAny | TAnyDefinedBy _ | TRef _ | TField _ -> t
  in
  let body = function
    | BType (t, o) -> BType (typ 0 t, o)
    | BContaining t -> BContaining (typ 0 t)
    | BAbsent -> BAbsent
  in
  let ms = List.map (fun (m: modul) ->
      let assignments = List.filter_map (function
          | TypeAssign (n, t) -> Some (TypeAssign (n, typ 0 t))
          | ValueAssign (n, t, v) -> Some (ValueAssign (n, typ 0 t, v))
          | (TypeTemplate _ | ClassAssign _ | ClassAlias _ | ObjectAssign _ | ObjectSetAssign _) as a -> Some a  (* for the checks of IMPORTS *))
          m.assignments
      in
      let directives = List.map (fun db ->
          { db with db_cases = List.map (fun (v, b) -> (v, body b)) db.db_cases;
                    db_fallback = (match db.db_fallback with FbBody b -> FbBody (body b) | f -> f) })
          m.directives
      in
      { m with assignments; directives })
      ms
  in
  List.map (fun (m: modul) ->
      match Hashtbl.find_opt extra m.mname with
      | Some l -> { m with assignments = m.assignments @ List.rev l }
      | None -> m)
    ms


(* Information object classes (X.681) and table constraints (X.682): a
   component `C.&Type ({Set}{@key})` (possibly under tags, SEQUENCE OF,
   CONTAINING, ...) whose key component is `C.&id ({Set})` generates a
   DEFINED-BY table, with a case per object of Set (the fallback is the
   declared component, i.e. ANY, if Set is extensible, NONE otherwise).
   The other field references are replaced with their types (ANY for a
   type field). *)
let builtin_classes = [
  "TYPE-IDENTIFIER", { cl_fields = [FsValue ("id", TBuiltin "OBJECT IDENTIFIER", false); FsType ("Type", false)];
                       cl_syntax = Some [SField "Type"; SWord "IDENTIFIED"; SWord "BY"; SField "id"] };
  "ABSTRACT-SYNTAX", { cl_fields = [FsValue ("id", TBuiltin "OBJECT IDENTIFIER", false); FsType ("Type", false); FsOther "property"];
                       cl_syntax = Some [SField "Type"; SWord "IDENTIFIED"; SWord "BY"; SField "id";
                                         SOpt [SWord "HAS"; SWord "PROPERTY"; SField "property"]] };
]

let resolve_ioc (ms: modul list) : modul list =
  let all = List.concat_map (fun (m: modul) -> m.assignments) ms in
  let classes = Hashtbl.create 7 in
  List.iter (fun (n, c) -> Hashtbl.replace classes n c) builtin_classes;
  List.iter (function
      | ClassAssign (n, c) ->
        if Hashtbl.mem classes n then error "class %s defined twice" n;
        Hashtbl.replace classes n c
      | _ -> ())
    all;
  let aliases = List.filter_map (function
      | ClassAlias (n, c) -> Some (n, c)
      | TypeAssign (n, TRef c) when Parse.is_class_name n && Parse.is_class_name c -> Some (n, c)
      | _ -> None) all in
  let rec fix () =
    let changed = ref false in
    List.iter (fun (n, c) ->
        if not (Hashtbl.mem classes n) && Hashtbl.mem classes c then begin
          Hashtbl.replace classes n (Hashtbl.find classes c); changed := true
        end) aliases;
    if !changed then fix ()
  in
  fix ();
  List.iter (function ClassAlias (n, c) when not (Hashtbl.mem classes n) -> error "%s: unknown class %s" n c | _ -> ()) all;
  let is_class n = Hashtbl.mem classes n in
  let cls where n = match Hashtbl.find_opt classes n with
    | Some c -> c
    | None -> error "%s: unknown class %s" where n
  in
  let objects = Hashtbl.create 17 in
  List.iter (function
      | ObjectAssign (n, c, r) when is_class c ->
        if Hashtbl.mem objects n then error "object %s defined twice" n;
        Hashtbl.replace objects n (`Raw (c, r))
      | ValueAssign (n, TRef c, VName o) when is_class c ->
        if Hashtbl.mem objects n then error "object %s defined twice" n;
        Hashtbl.replace objects n (`Alias o)
      | ValueAssign (n, TRef c, _) when is_class c -> error "object %s: expected { ... } or an object reference" n
      | _ -> ())
    all;
  let parsed = Hashtbl.create 17 in
  let rec obj depth n =
    if depth > 100 then error "object %s: circular definition" n;
    match Hashtbl.find_opt objects n with
    | Some (`Raw (c, r)) ->
      (match Hashtbl.find_opt parsed n with
       | Some x -> x
       | None -> let x = Parse.parse_object (cls n c) r in Hashtbl.replace parsed n x; x)
    | Some (`Alias o) -> obj (depth + 1) o
    | None -> error "unknown information object %s" n
  in
  let sets = Hashtbl.create 7 in
  List.iter (function
      | ObjectSetAssign (n, c, o) ->
        if not (is_class c) then error "%s: value sets are not supported (or unknown class %s)" n c;
        if Hashtbl.mem sets n then error "object set %s defined twice" n;
        Hashtbl.replace sets n (c, o)
      | _ -> ())
    all;
  let rec flatten depth c (o: obj_set) =
    if depth > 100 then error "circular object set definition";
    List.fold_left (fun (acc, ext) e -> match e with
        | EObject n -> (acc @ [obj 0 n], ext)
        | EInline r -> (acc @ [Parse.parse_object (cls "object set" c) r], ext)
        | ESet n ->
          (match Hashtbl.find_opt sets n with
           | Some (c', o') -> let l, e' = flatten (depth + 1) c' o' in (acc @ l, ext || e')
           | None -> error "unknown object set %s" n))
      ([], o.ext) o.elems
  in
  let field_kind c f =
    match List.find_opt (function FsType (n, _) | FsValue (n, _, _) | FsOther n -> n = f) (cls (c ^ ".&" ^ f) c).cl_fields with
    | Some k -> k
    | None -> error "class %s has no field &%s" c f
  in
  let rec head_field = function
    | TField _ -> true
    | TConstrained (t, _) -> head_field t
    | _ -> false
  in
  (* Replace the field references with their types *)
  let rec strip (t: typ) : typ =
    match t with
    | TField (c, f) ->
      (match field_kind c f with
       | FsType _ -> TAny
       | FsValue (_, t, _) -> strip t
       | FsOther _ -> error "%s.&%s: only type and value fields are supported" c f)
    | TConstrained (_, CTable (_, Some k)) ->
      error "{@%s}: component relation constraints are supported only in the components of a SEQUENCE type assignment" k
    | TConstrained (t, CTable (_, None)) -> strip t
    | TConstrained (t, CContaining t') when head_field t' -> ignore (strip t'); strip t
    | TConstrained (t, c) -> TConstrained (strip t, strip_c c)
    | TSequence cs -> TSequence (List.map comp cs)
    | TSet cs -> TSet (List.map comp cs)
    | TSequenceOf (c, t) -> TSequenceOf (Option.map strip_c c, strip t)
    | TSetOf (c, t) -> TSetOf (Option.map strip_c c, strip t)
    | TChoice alts -> TChoice (List.map (fun (n, t) -> (n, strip t)) alts)
    | TTagged (c, n, m, t) -> TTagged (c, n, m, strip t)
    | TBuiltin _ | TInteger _ | TEnumerated _ | TBitString _ | TAny | TAnyDefinedBy _ | TRef _ | TInst _ -> t
  and comp = function
    | Field (n, t, d) -> Field (n, strip t, d)
    | ComponentsOf t -> ComponentsOf (strip t)
  and strip_c (c: constr) : constr =
    match c with
    | CSize c -> CSize (strip_c c)
    | CUnion l -> CUnion (List.map strip_c l)
    | CContaining t -> CContaining (strip t)
    | CWithComponent c -> CWithComponent (strip_c c)
    | CWithComponents (p, l) -> CWithComponents (p, List.map (fun (n, c, pr) -> (n, Option.map strip_c c, pr)) l)
    | CRange _ | CSingle _ | CTable _ -> c
  in
  (* The occurrences of C.&f ({Set}{@key}) in a component (not in nested
     SEQUENCE, SET or CHOICE types), and their replacement *)
  let rec keyed (t: typ) =
    match t with
    | TConstrained (TField (c, f), CTable (set, Some k)) -> [(c, f, set, k)]
    | TConstrained (t, CContaining t') -> keyed t @ keyed t'
    | TConstrained (t, _) | TTagged (_, _, _, t) | TSequenceOf (_, t) | TSetOf (_, t) -> keyed t
    | _ -> []
  in
  let rec replace u (t: typ) : typ =
    match t with
    | TConstrained ((TField _ as x), CTable (_, Some _)) -> (match u with Some u -> u | None -> x)
    | TConstrained (t, CContaining t') -> TConstrained (replace u t, CContaining (replace u t'))
    | TConstrained (t, c) -> TConstrained (replace u t, c)
    | TTagged (c, n, m, t) -> TTagged (c, n, m, replace u t)
    | TSequenceOf (c, t) -> TSequenceOf (c, replace u t)
    | TSetOf (c, t) -> TSetOf (c, replace u t)
    | _ -> t
  in
  let rec peel = function TTagged (_, _, _, t) -> peel t | t -> t in
  let user_dbs = List.concat_map (fun (m: modul) -> List.map (fun db -> db.db_type) m.directives) ms in
  let sequence n (cs: component list) : defined_by option =
    let deps = List.concat_map (function
        | Field (f, t, d) -> List.map (fun x -> (f, t, d, x)) (keyed t)
        | ComponentsOf _ -> []) cs in
    match deps with
    | [] -> None
    | _ :: _ :: _ -> error "%s: only one component relation constraint {@key} per SEQUENCE is supported" n
    | [(f, t, d, (c, fl, set, k))] ->
      let where = Printf.sprintf "%s.%s ({@%s})" n f k in
      let kt = match List.find_opt (function Field (n', _, _) -> n' = k | ComponentsOf _ -> false) cs with
        | Some (Field (_, kt, _)) -> kt
        | _ -> error "%s: %s has no component %s" where n k
      in
      let rec key_field = function
        | TField (c', idf) -> (c', idf)
        | TConstrained (t, _) | TTagged (_, _, _, t) -> key_field t
        | _ -> error "%s: the key component %s must be a field reference %s.&id ({Set})" where k c
      in
      let _, idf = key_field kt in
      (match field_kind c fl with
       | FsType _ -> ()
       | _ -> error "%s: %s.&%s must be a type field" where c fl);
      (match field_kind c idf with
       | FsValue _ -> ()
       | _ -> error "%s: %s.&%s must be a value field" where c idf);
      if List.mem n user_dbs then begin
        Printf.eprintf "Warning: %s: the --#DEFINED-BY directive replaces the table constraint\n" where;
        None
      end else begin
        let objs, ext = flatten 0 c set in
        let seen = Hashtbl.create 7 in
        let cases = List.filter_map (fun settings ->
            let kv = match List.assoc_opt idf settings with
              | Some (Parse.SetValue v) -> v
              | _ -> error "%s: an object of the set has no &%s" where idf
            in
            if Hashtbl.mem seen kv then None else begin
              Hashtbl.add seen kv ();
              match List.assoc_opt fl settings, d with
              | _, DDefault _ -> error "%s: a dependent component cannot have a DEFAULT" where
              | Some (Parse.SetType u), _ -> Some (kv, BType (strip (replace (Some u) (peel t)), d = DOptional))
              | None, DOptional -> Some (kv, BAbsent)
              | None, _ -> error "%s: an object of the set has no &%s, but %s is not OPTIONAL" where fl f
              | Some _, _ -> error "%s: &%s is not a type" where fl
            end)
            objs
        in
        Some { db_type = n; db_field = f; db_key = Some k; db_cases = cases;
               db_fallback = (if ext then FbDeclared else FbNone); db_line = 0 }
      end
  in
  List.map (fun (m: modul) ->
      let dbs = ref [] in
      let assignments = List.filter_map (function
          | TypeAssign (n, TRef c) when Hashtbl.mem classes n -> Some (ClassAlias (n, c))
          | TypeAssign (n, TSequence cs) ->
            (match sequence n cs with Some db -> dbs := db :: !dbs | None -> ());
            Some (TypeAssign (n, strip (TSequence (List.map (function
                | Field (f, t, d) -> Field (f, replace None t, d)
                | c -> c) cs))))
          | TypeAssign (n, t) -> Some (TypeAssign (n, strip t))
          | ValueAssign (n, TRef c, v) when is_class c -> ignore v; Some (ObjectAssign (n, c, []))
          | ValueAssign (n, t, v) -> Some (ValueAssign (n, strip t, v))
          | ObjectAssign (n, c, r) when not (is_class c) -> Some (ValueAssign (n, TRef c, Parse.parse_value r))
          | a -> Some a)
          m.assignments
      in
      { m with assignments; directives = m.directives @ List.rev !dbs })
    ms

type result = {
  env: env;
  order: string list;           (* definitions, dependencies first *)
  roots: string list;           (* default roots: types of the main module referenced by no other type *)
  user_names: string list;      (* the type assignments, in source order *)
  keep: string list;            (* the KEEP-BYTES definitions *)
}

(* Elaborate the main module `m` and the modules it imports from (`deps`),
   with the KEEP-BYTES types and components `keep` (T or T.c) *)
let elaborate ?(lax_size_of = false) ?(max_int_union = 256) ?(keep = []) (m: modul) (deps: modul list) : result =
  let env = {
    mname = m.mname; td = m.tag_default; type_td = Hashtbl.create 17;
    types = Hashtbl.create 17; values = Hashtbl.create 17; dbs = Hashtbl.create 17;
    lax_size_of; max_int_union; defs = Hashtbl.create 17;
    state = Hashtbl.create 17; order = []; user = Hashtbl.create 17;
    keep = Hashtbl.create 7; keep_alias = Hashtbl.create 7; keep_comps = Hashtbl.create 7;
  } in
  let m, deps = match expand_params (resolve_ioc (expand_params (m :: deps))) with
    | m :: deps -> m, deps
    | [] -> assert false
  in
  let ms = m :: deps in
  List.iter (fun (m': modul) ->
      if List.length (List.filter (fun (m'': modul) -> m''.mname = m'.mname) ms) > 1 then
        error "module %s is given twice" m'.mname)
    ms;
  let names_of (m: modul) = List.filter_map (function
      | TypeAssign (n, t) ->
        let n' = mangle n in
        if Hashtbl.mem env.types n' then error "type %s defined twice" n;
        Hashtbl.replace env.types n' t;
        Hashtbl.replace env.type_td n' m.tag_default;
        Hashtbl.replace env.user n' n;
        Some n'
      | ValueAssign (n, t, v) ->
        if Hashtbl.mem env.values n then error "value %s defined twice" n;
        Hashtbl.replace env.values n (t, v); None
      | TypeTemplate _ | ClassAssign _ | ClassAlias _ | ObjectAssign _ | ObjectSetAssign _ -> None)
      m.assignments
  in
  let main_names = names_of m in
  let names = main_names @ List.concat_map names_of deps in
  (* The types of the prelude, elaborated only if used *)
  let prelude = Parse.parse_string Prelude.text in
  List.iter (function
      | TypeAssign (n, t) ->
        let n' = mangle n in
        if not (Hashtbl.mem env.types n') then begin
          Hashtbl.replace env.types n' t;
          Hashtbl.replace env.type_td n' prelude.tag_default;
          Hashtbl.replace env.user n' n
        end
      | _ -> ())
    prelude.assignments;
  (* IMPORTS: the symbols must be defined by the given modules *)
  List.iter (fun (m: modul) ->
      List.iter (fun (from, syms) ->
          match List.find_opt (fun (m': modul) -> m'.mname = from) ms with
          | None -> error "%s imports from %s: please also give the file of module %s" m.mname from from
          | Some m' ->
            List.iter (fun s ->
                let defined = List.exists (function
                    | TypeAssign (n, _) | ValueAssign (n, _, _) | TypeTemplate (n, _, _)
                    | ClassAssign (n, _) | ClassAlias (n, _) | ObjectAssign (n, _, _) | ObjectSetAssign (n, _, _) -> n = s) m'.assignments in
                if not defined then error "%s imports %s from %s, which does not define it" m.mname s from)
              syms)
        m.imports)
    ms;
  List.iter (fun (m: modul) ->
      List.iter (fun db ->
          let n = mangle db.db_type in
          if Hashtbl.mem env.dbs n then error "line %d: a second DEFINED-BY table for %s" db.db_line db.db_type;
          Hashtbl.replace env.dbs n db)
        m.directives)
    ms;
  let keep = keep @ List.concat_map (fun (m: modul) -> m.keep_bytes) ms in
  List.iter (fun a ->
      match String.index_opt a '.' with
      | Some i ->
        let t = mangle (String.sub a 0 i) and c = mangle (String.sub a (i + 1) (String.length a - i - 1)) in
        if not (Hashtbl.mem env.types t) then error "KEEP-BYTES: unknown type %s" a;
        Hashtbl.replace env.keep_comps (t ^ "." ^ c) (ref false)
      | None ->
        let n = mangle a in
        if not (Hashtbl.mem env.types n) then error "KEEP-BYTES: unknown type %s" a;
        Hashtbl.replace env.keep n ())
    keep;
  List.iter (elab_def env) names;
  Hashtbl.iter (fun c used -> if not !used then error "KEEP-BYTES: unknown component %s" c) env.keep_comps;
  Hashtbl.iter (fun n db ->
      if not (Hashtbl.mem env.defs n) then error "line %d: DEFINED-BY: unknown type %s" db.db_line db.db_type)
    env.dbs;
  let referenced =
    List.concat_map (fun n -> refs (Hashtbl.find env.types n)) names @
    Hashtbl.fold (fun _ db acc ->
        List.concat_map (fun (_, b) -> body_refs b) db.db_cases @
        (match db.db_fallback with FbBody b -> body_refs b | _ -> []) @ acc) env.dbs []
  in
  let roots = List.filter (fun n -> not (List.mem n referenced)) main_names in
  let order = List.rev env.order in
  { env; order; roots; user_names = names; keep = List.filter (Hashtbl.mem env.keep) order }
