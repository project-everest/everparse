(* Elaboration: name resolution, tagging (X.680 31), AUTOMATIC tagging
   (X.680 25.3), COMPONENTS OF, constraints and DEFAULT values. Anonymous
   SEQUENCE, SET and CHOICE types are hoisted to named definitions, so that
   each of them gets a named C type. *)

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

type fdeco =
  | FPlain
  | FOptional
  | FDefault of id * term * string option * string   (* id, terminal, restriction, F* literal *)

type field = { fname: string; fnode: node; fdeco: fdeco }

type alt =
  | ALeaf of string * id * cnode    (* name, identifier, content *)
  | ASub of string * string         (* name, a named CHOICE (flattened) *)

type def =
  | DStruct of bool * field list    (* SET?, components *)
  | DChoice of alt list
  | DNode of node

type env = {
  m: modul;
  types: (string, typ) Hashtbl.t;           (* mangled name -> ASN.1 type *)
  values: (string, typ * value) Hashtbl.t;
  defs: (string, def) Hashtbl.t;
  state: (string, bool) Hashtbl.t;          (* false: in progress *)
  mutable order: string list;               (* reverse topological order *)
  user: (string, string) Hashtbl.t;         (* mangled -> ASN.1 name *)
}

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
    | DStruct _ -> (match resolve env n with RILC (id, c) -> Some (id, c) | _ -> None)
    | DChoice _ -> None
    end
  | NAny -> None

let content_cons env c =
  match struct_content env c with
  | CTerm _ -> false
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
  | VBool _ -> error "expected an INTEGER value"

let rec bool_value env (v: value) : bool =
  match v with
  | VBool b -> b
  | VName n ->
    (match Hashtbl.find_opt env.values n with
     | Some (_, v) -> bool_value env v
     | None -> error "unknown value %s" n)
  | VInt _ -> error "expected a BOOLEAN value"

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
    elab_named env name t

and elab_named env name t =
  if Hashtbl.mem env.state name then error "name clash: %s is defined twice (hoisted anonymous types are named <Type>_<component>)" name;
  Hashtbl.replace env.state name false;
  let d = match t with
    | TSequence cs -> DStruct (false, fields env name cs)
    | TSet cs -> DStruct (true, fields env name cs)
    | TChoice alts -> DChoice (choice env name alts)
    | _ -> DNode (node env (name ^ "_body") t)
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
  | TSequenceOf (c, t') | TSetOf (c, t') ->
    let set = (match t with TSetOf _ -> true | _ -> false) in
    let ne = match c with
      | None -> false
      | Some (CSize (CRange (Val 1, Max))) -> true
      | Some (CSize (CRange (Val 0, Max))) -> false
      | Some _ -> error "%s: only SIZE (1..MAX) is supported on SEQUENCE OF / SET OF" ctx
    in
    NILC (univ ~cons:true (if set then 17 else 16), COf (set, ne, node env (ctx ^ "_elt") t'))
  | TTagged (cls, num, mode, t') ->
    let inner = node env ctx t' in
    let implicit = match mode with
      | TImplicit -> true
      | TExplicit -> false
      | TDefault -> env.m.tag_default <> DExplicit
    in
    begin match resolve env inner with
    | RILC (_, c) when implicit -> NILC ({ cls; num; cons = content_cons env c }, c)
    | _ -> NILC ({ cls; num; cons = true }, CPrefixed inner)  (* X.680 31.2.7 *)
    end
  | TConstrained (t', c) ->
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
        NILC (id, CTerm (small_integer_term, Some (Printf.sprintf "(RESTRICT_INT_IN [%s])" (String.concat "; " (List.map fstar_int vs)))))
      | CSize _ -> error "%s: SIZE constraint on INTEGER" ctx
      end
    | Some (id, CTerm ({ tk = "ASN1_OCTETSTRING"; _ } as tm, None)), CSize sz ->
      let lo, hi = match sz with
        | CRange (Val lo, Max) when lo >= 0 -> lo, "None"
        | CRange (Val lo, Val hi) when lo >= 0 -> lo, Printf.sprintf "(Some %d)" hi
        | CRange (Min, Val hi) -> 0, Printf.sprintf "(Some %d)" hi
        | CSingle [n] when n >= 0 -> n, Printf.sprintf "(Some %d)" n
        | _ -> error "%s: unsupported SIZE constraint" ctx
      in
      NILC (id, CTerm (tm, Some (Printf.sprintf "(RESTRICT_SIZE %d %s)" lo hi)))
    | _ -> error "%s: constraints are supported on INTEGER and on the SIZE of OCTET STRING only" ctx
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
  if env.m.tag_default = DAutomatic && not (List.exists (fun (_, t) -> tagged t) own)
  then List.mapi (fun i (n, t) -> (n, TTagged (Context, i, TImplicit, t))) all
  else all

and fields env name cs : field list =
  let own = List.filter_map (function Field (n, t, _) -> Some (n, t) | _ -> None) cs in
  let all = components env name cs in
  let tagged = auto_tag env own (List.map (fun (n, t, _) -> (n, t)) all) in
  let seen = Hashtbl.create 7 in
  List.map2 (fun (n, src, d) (_, t) ->
      let fname = mangle n in
      if Hashtbl.mem seen fname then error "%s: duplicate component %s" name n;
      Hashtbl.add seen fname ();
      let fnode = node env (name ^ "_" ^ fname) t in
      let fdeco = match d with
        | DPlain -> FPlain
        | DOptional -> FOptional
        | DDefault v ->
          begin match resolve_struct env fnode with
          | Some (id, CTerm (tm, r)) ->
            let lit = match tm.tk, tm.ibound with
              | "ASN1_BOOLEAN", _ -> string_of_bool (bool_value env v)
              | _, Some b ->
                let bytes = int_bytes (int_value env src v) in
                Printf.sprintf "(mk_int_lit %s [%s] ())" b
                  (String.concat "; " (List.map (Printf.sprintf "%duy") bytes))
              | _ -> error "%s.%s: DEFAULT is supported on BOOLEAN and INTEGER only" name n
            in
            FDefault (id, tm, r, lit)
          | _ -> error "%s.%s: DEFAULT is supported on BOOLEAN and INTEGER only" name n
          end
      in
      { fname; fnode; fdeco })
    all tagged

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
  | TSequenceOf (_, t) | TSetOf (_, t) | TTagged (_, _, _, t) | TConstrained (t, _) -> refs t
  | _ -> []

type result = {
  env: env;
  order: string list;           (* definitions, dependencies first *)
  roots: string list;           (* default roots: types referenced by no other type *)
  user_names: string list;      (* the type assignments, in source order *)
}

let elaborate (m: modul) : result =
  let env = {
    m; types = Hashtbl.create 17; values = Hashtbl.create 17; defs = Hashtbl.create 17;
    state = Hashtbl.create 17; order = []; user = Hashtbl.create 17;
  } in
  let names = List.filter_map (function
      | TypeAssign (n, t) ->
        let n' = mangle n in
        if Hashtbl.mem env.types n' then error "type %s defined twice" n;
        Hashtbl.replace env.types n' t;
        Hashtbl.replace env.user n' n;
        Some n'
      | ValueAssign (n, t, v) -> Hashtbl.replace env.values n (t, v); None)
      m.assignments
  in
  List.iter (elab_def env) names;
  let referenced = List.concat_map (fun n -> refs (Hashtbl.find env.types n)) names in
  let roots = List.filter (fun n -> not (List.mem n referenced)) names in
  { env; order = List.rev env.order; roots; user_names = names }
