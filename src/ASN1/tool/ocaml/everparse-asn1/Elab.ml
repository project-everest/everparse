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
  defs: (string, def) Hashtbl.t;
  state: (string, bool) Hashtbl.t;          (* false: in progress *)
  mutable order: string list;               (* reverse topological order *)
  user: (string, string) Hashtbl.t;         (* mangled -> ASN.1 name *)
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
  | VBool _ | VOid _ -> error "expected an INTEGER value"

let rec bool_value env (v: value) : bool =
  match v with
  | VBool b -> b
  | VName n ->
    (match Hashtbl.find_opt env.values n with
     | Some (_, v) -> bool_value env v
     | None -> error "unknown value %s" n)
  | VInt _ | VOid _ -> error "expected a BOOLEAN value"

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
  | VInt _ | VBool _ -> error "expected an OBJECT IDENTIFIER value"

(* Resolve the value references in the bounds of a constraint *)
let rec norm_constr env (c: constr) : constr =
  let b = function
    | BRef s -> Val (int_value env (TInteger []) (VName s))
    | x -> x
  in
  match c with
  | CSize c -> CSize (norm_constr env c)
  | CRange (lo, hi) -> CRange (b lo, b hi)
  | CSingle l -> CSingle (List.map b l)
  | CContaining _ -> c

(* The types under the outermost tags *)
let rec under_tags f = function
  | TTagged (c, n, m, t) -> TTagged (c, n, m, under_tags f t)
  | t -> f t

let fstar_int i = if i < 0 then Printf.sprintf "(%d)" i else string_of_int i

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
  Hashtbl.replace env.state name false;
  let d = match t, Hashtbl.find_opt env.dbs name with
    | TSequence cs, Some db -> DAdb (adb env name cs db)
    | _, Some db -> error "line %d: DEFINED-BY %s: not a SEQUENCE" db.db_line db.db_type
    | TSequence cs, None -> DStruct (false, fields env name cs)
    | TSet cs, None -> DStruct (true, fields env name cs)
    | TChoice alts, None -> DChoice (choice env name alts)
    | _, None -> DNode (node env (name ^ "_body") t)
  in
  Hashtbl.replace env.defs name d;
  Hashtbl.replace env.state name true;
  env.order <- name :: env.order

(* Elaborate a type into a node; anonymous constructed types are hoisted
   under the name `ctx` *)
and node env (ctx: string) (t: typ) : node =
  match t with
  | TSequence _ | TSet _ | TChoice _ ->
    if Hashtbl.mem env.types ctx then error "name clash: anonymous type %s" ctx;
    elab_named env ctx t; NRef ctx
  | TRef r -> let r = mangle r in elab_def env r; NRef r
  | TBuiltin s -> let id, tm = builtin s in NILC (id, CTerm (tm, None))
  | TInteger _ -> NILC (univ 2, CTerm (integer_term, None))
  | TEnumerated items ->
    let vs = List.map snd (enum_values items) in
    NILC (univ 10, CTerm (small_integer_term,
      Some (Printf.sprintf "(RESTRICT_INT_IN [%s])" (String.concat "; " (List.map fstar_int vs)))))
  | TBitString -> NILC (univ 3, CTerm (bitstring_term, None))
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
    | RILC (_, c) when implicit -> NILC ({ cls; num; cons = content_cons env c }, c)
    | _ -> NILC ({ cls; num; cons = true }, CPrefixed inner)  (* X.680 31.2.7 *)
    end
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
      | CSize _ | CContaining _ -> error "%s: SIZE constraint on INTEGER" ctx
      end
    | Some (id, CTerm ({ tk = ("ASN1_OCTETSTRING" | "ASN1_UTF8STRING" | "ASN1_BMPSTRING"
                             | "ASN1_UNIVERSALSTRING" | "ASN1_PRINTABLESTRING" | "ASN1_IA5STRING"
                             | "ASN1_VISIBLESTRING" | "ASN1_NUMERICSTRING" | "ASN1_TELETEXSTRING"
                             | "ASN1_VIDEOTEXSTRING" | "ASN1_GRAPHICSTRING" | "ASN1_GENERALSTRING"
                             | "ASN1_OBJECTDESCRIPTOR"); _ } as tm, None)), CSize sz ->
      let lo, hi = match sz with
        | CRange (Val lo, Max) when lo >= 0 -> lo, "None"
        | CRange (Val lo, Val hi) when lo >= 0 -> lo, Printf.sprintf "(Some %d)" hi
        | CRange (Min, Val hi) -> 0, Printf.sprintf "(Some %d)" hi
        | CSingle [Val n] when n >= 0 -> n, Printf.sprintf "(Some %d)" n
        | _ -> error "%s: unsupported SIZE constraint" ctx
      in
      NILC (id, CTerm (tm, Some (Printf.sprintf "(RESTRICT_SIZE %d %s)" lo hi)))
    | _ -> error "%s: constraints are supported on INTEGER and on the SIZE of OCTET STRING and character strings only" ctx
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
  match tm.tk, tm.ibound with
  | "ASN1_BOOLEAN", _ -> string_of_bool (bool_value env v)
  | "ASN1_OID", _ ->
    Printf.sprintf "(mk_oid [%s])" (String.concat "; " (List.map string_of_int (oid_value env v)))
  | _, Some b ->
    let bytes = int_bytes (int_value env src v) in
    Printf.sprintf "(mk_int_lit %s [%s] ())" b
      (String.concat "; " (List.map (Printf.sprintf "%duy") bytes))
  | _ -> error "%s: only BOOLEAN, INTEGER and OBJECT IDENTIFIER values are supported" where

and elab_field env owner ((n, src, d, t): string * typ * deco * typ) : field =
  let fname = mangle n in
  let fnode = node env (owner ^ "_" ^ fname) t in
  let fdeco = match d with
    | DPlain -> FPlain
    | DOptional -> FOptional
    | DDefault v ->
      let where = Printf.sprintf "%s.%s: DEFAULT" owner n in
      begin match terminal_of env fnode with
      | Some (_, _, Some _, { tk = "ASN1_OID"; _ }) -> error "%s: not supported on OBJECT IDENTIFIER" where
      | Some (id, tm, r, ltm) -> FDefault (id, tm, r, literal env where src ltm v)
      | None -> error "%s: supported on BOOLEAN and INTEGER only (possibly EXPLICIT-tagged, unconstrained)" where
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
  let key = elab_field env name key_c in
  let key_id, key_term, ltm = match terminal_of env key.fnode with
    | Some (id, tm, None, ltm) -> id, tm, ltm
    | Some (_, _, Some _, _) -> error "%s: the key component %s must not be constrained" where key_n
    | None -> error "%s: the key component %s must be a BOOLEAN, INTEGER or OBJECT IDENTIFIER" where key_n
  in
  (* The components after the key, other than the dependent one, are shared *)
  let after = List.filteri (fun i _ -> i > key_i) comps in
  let shared = List.map (fun ((n, _, _, _) as c) -> if n = dep_n then None else Some (elab_field env name c)) after in
  let with_dep owner (b: case_body option) : field list =
    let dep_field = match b with
      | None -> Some (elab_field env name dep)
      | Some BAbsent -> None
      | Some (BType (t, opt)) ->
        Some (elab_field env owner (dep_n, t, (if opt then DOptional else DPlain), under_tags (fun _ -> t) dep_t))
      | Some (BContaining t) ->
        Some (elab_field env owner (dep_n, dep_src, DPlain, under_tags (fun d -> TConstrained (d, CContaining t)) dep_t))
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
  | TConstrained (t, CContaining t') -> refs t @ refs t'
  | TConstrained (t, _) -> refs t
  | _ -> []

let body_refs = function
  | BAbsent -> []
  | BType (t, _) | BContaining t -> refs t

type result = {
  env: env;
  order: string list;           (* definitions, dependencies first *)
  roots: string list;           (* default roots: types of the main module referenced by no other type *)
  user_names: string list;      (* the type assignments, in source order *)
}

(* Elaborate the main module `m` and the modules it imports from (`deps`) *)
let elaborate ?(lax_size_of = false) (m: modul) (deps: modul list) : result =
  let env = {
    mname = m.mname; td = m.tag_default; type_td = Hashtbl.create 17;
    types = Hashtbl.create 17; values = Hashtbl.create 17; dbs = Hashtbl.create 17;
    lax_size_of; defs = Hashtbl.create 17;
    state = Hashtbl.create 17; order = []; user = Hashtbl.create 17;
  } in
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
        Hashtbl.replace env.values n (t, v); None)
      m.assignments
  in
  let main_names = names_of m in
  let names = main_names @ List.concat_map names_of deps in
  (* IMPORTS: the symbols must be defined by the given modules *)
  List.iter (fun (m: modul) ->
      List.iter (fun (from, syms) ->
          match List.find_opt (fun (m': modul) -> m'.mname = from) ms with
          | None -> error "%s imports from %s: please also give the file of module %s" m.mname from from
          | Some m' ->
            List.iter (fun s ->
                let defined = List.exists (function
                    | TypeAssign (n, _) | ValueAssign (n, _, _) -> n = s) m'.assignments in
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
  List.iter (elab_def env) names;
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
  { env; order = List.rev env.order; roots; user_names = names }
