(* Generation of the F* modules:
   - `M.fst`: the schema, as `ASN1.Base` terms (`k_T` for each type `T`);
   - `M.Pulse.fst`: a named C type for each SEQUENCE, SET, CHOICE and
     OPTIONAL/DEFAULT component, the impl descriptors (`d_T`) that map them
     to the schema, and the extraction roots `validate_T`, `parse_T`,
     `write_T` and `write_T_typed` for each root type `T`, plus
     `to_writer_T` for a type `T` (root or not) with KEEP-BYTES: its C
     type `T_kept` pairs its value and the bytes it was parsed from. *)

open Ast
open Elab

let buf = Buffer.create 65536
let p fmt = Printf.bprintf buf fmt
let sp = Printf.sprintf

let keywords = [
  (* F* *)
  "and"; "as"; "assert"; "assume"; "attributes"; "begin"; "by"; "calc"; "class";
  "decreases"; "default"; "effect"; "else"; "end"; "ensures"; "exception";
  "exists"; "false"; "forall"; "friend"; "fun"; "function"; "if"; "in";
  "include"; "inline"; "inline_for_extraction"; "instance"; "irreducible";
  "let"; "logic"; "match"; "module"; "new"; "noeq"; "noextract"; "of"; "open";
  "opaque"; "private"; "rec"; "reifiable"; "reflectable"; "requires"; "returns";
  "then"; "total"; "true"; "try"; "type"; "unfold"; "unfoldable"; "unopteq";
  "val"; "when"; "with"; "fn"; "mut"; "ghost"; "atomic"; "prop"; "x";
  (* C *)
  "auto"; "break"; "case"; "char"; "const"; "continue"; "do"; "double"; "enum";
  "extern"; "float"; "for"; "goto"; "int"; "long"; "register"; "return";
  "short"; "signed"; "sizeof"; "static"; "struct"; "switch"; "typedef";
  "union"; "unsigned"; "void"; "volatile"; "while"; "bool"; "tag"; "val";
]

let field_name f = if List.mem f keywords then f ^ "_" else f

type ctx = {
  r: result;
  spec: string;        (* the spec module name *)
  keep: string list;   (* the KEEP-BYTES types (mangled) *)
}

let is_keep ctx n = List.mem n ctx.keep

let def ctx n = def_of ctx.r.env n
let is_ilc ctx n = match resolve ctx.r.env (NRef n) with RILC _ -> true | _ -> false

(* Schema terms *)

let rec kexpr (n: node) = match n with
  | NRef r -> "k_" ^ r
  | NAny -> "ASN1_ANY_ILC"
  | NILC (id, c) -> sp "(ASN1_ILC %s %s)" (idexpr id) (cexpr c)

and cexpr (c: cnode) = match c with
  | CTerm (t, None) -> sp "(ASN1_TERMINAL %s)" t.tk
  | CTerm (t, Some r) -> sp "(ASN1_RESTRICTED_TERMINAL %s %s)" t.tk r
  | CRef r -> "c_" ^ r
  | COf (set, ne, n) -> sp "(%s %b %s)" (if set then "ASN1_SET_OF" else "ASN1_SEQUENCE_OF") ne (kexpr n)
  | CPrefixed n | CContaining n -> sp "(ASN1_PREFIXED %s)" (kexpr n)

(* The default value of a DEFAULT component, defined in the spec module *)
let dv_name _ (f: field) = sp "dv_%s_%s" f.fowner f.fname

(* The components of an ANY DEFINED BY, each once *)
let adb_fields (a: adb) : field list =
  let rest = List.concat_map (fun c -> c.cfields) a.cases @ (match a.fallback with Some l -> l | None -> []) in
  let seen = Hashtbl.create 7 in
  a.prefix @ [a.key] @ List.filter (fun f ->
      let k = (f.fowner, f.fname) in
      if Hashtbl.mem seen k then false else (Hashtbl.add seen k (); true)) rest

let gen_dv n (f: field) = match f.fdeco with
  | FDefault (_, t, None, lit) ->
    p "noextract\nlet %s : asn1_key_lit %s = %s\n\n" (dv_name n f) t.tk lit
  | FDefault (_, t, Some r, lit) ->
    p "noextract\nlet %s : (l: asn1_key_lit %s { restriction_pred %s (key_of_lit %s l) = true }) =\n  let l : asn1_key_lit %s = %s in\n  assert_norm (restriction_pred_lit #%s %s %s);\n  restriction_pred_lit_correct #%s %s l;\n  l\n\n"
      (dv_name n f) t.tk r t.tk t.tk lit t.tk r lit t.tk r
  | _ -> ()

let dkexpr n (f: field) = match f.fdeco with
  | FPlain -> sp "(ASN1_PLAIN_ILC %s)" (kexpr f.fnode)
  | FOptional -> sp "(ASN1_OPTION_ILC %s)" (kexpr f.fnode)
  | FDefault (id, t, None, _) -> sp "(ASN1_DEFAULT_TERMINAL %s #%s %s)" (idexpr id) t.tk (dv_name n f)
  | FDefault (id, t, Some r, _) -> sp "(ASN1_DEFAULT_RESTRICTED_TERMINAL %s #%s %s %s)" (idexpr id) t.tk r (dv_name n f)

let items_expr n fields =
  List.fold_right (fun f acc -> sp "(ASN1_GEN_ITEMS_CONS _ _ %s _\n    %s)" (dkexpr n f) acc) fields "ASN1_GEN_ITEMS_NIL"

(* The CHOICE alternatives, flattened: each leaf with the path of
   constructors leading to it *)
let rec leaves ctx (n: string) : (string list * id * cnode) list =
  match def ctx n with
  | DChoice alts ->
    List.concat_map (function
        | ALeaf (a, id, c) -> [([n ^ "_" ^ a], id, c)]
        | ASub (a, r) -> List.map (fun (path, id, c) -> ((n ^ "_" ^ a) :: path, id, c)) (leaves ctx r))
      alts
  | _ -> error "internal error: %s is not a CHOICE" n

let gen_spec ctx (n: string) =
  let ilc_consts id c =
    p "noextract\nlet id_%s : asn1_id_t = %s\n\n" n id;
    p "noextract\nlet c_%s : asn1_content_k = %s\n\n" n c;
    p "noextract\nlet k_%s = ASN1_ILC id_%s c_%s\n\n" n n n
  in
  (match def ctx n with
   | DStruct (set, fields) ->
     List.iter (gen_dv n) fields;
     p "noextract\nlet items_%s =\n    %s\n\n" n (items_expr n fields);
     if set then
       ilc_consts "(mk_constant_constructed_id 17)" (sp "ASN1_SET _ items_%s (_ by (set_tac ()))" n)
     else begin
       p "noextract\nlet gitems_%s : asn1_gen_items_lk = mk_gitems items_%s (_ by (seq_tac ()))\n\n" n n;
       ilc_consts "(mk_constant_constructed_id 16)" (sp "ASN1_SEQUENCE gitems_%s" n)
     end
   | DChoice _ ->
     let ls = leaves ctx n in
     p "noextract\nlet lc_%s : list (asn1_id_t & asn1_content_k) = [\n%s]\n\n" n
       (String.concat ";\n" (List.map (fun (_, id, c) -> sp "    (%s, %s)" (idexpr id) (cexpr c)) ls));
     p "noextract\nlet pf_%s : squash (List.Tot.noRepeats (List.Tot.map fst lc_%s)) = _ by (choice_tac ())\n\n" n n;
     p "noextract\nlet k_%s = ASN1_CHOICE_ILC lc_%s pf_%s\n\n" n n n
   | DNode (NRef r) ->
     if is_ilc ctx r then begin
       p "noextract\nlet id_%s : asn1_id_t = id_%s\n\n" n r;
       p "noextract\nlet c_%s : asn1_content_k = c_%s\n\n" n r
     end;
     p "noextract\nlet k_%s = k_%s\n\n" n r
   | DNode NAny ->
     p "noextract\nlet k_%s = ASN1_ANY_ILC\n\n" n
   | DNode (NILC (id, c)) -> ilc_consts (idexpr id) (cexpr c)
   | DAdb a ->
     List.iter (gen_dv n) (adb_fields a);
     p "noextract\nlet items_%s =\n    %s\n\n" n (items_expr n a.prefix);
     let gitems suffix fields =
       p "noextract\nlet gitems_%s_%s : asn1_gen_items_lk = mk_gitems %s (_ by (seq_tac ()))\n\n" n suffix (items_expr n fields)
     in
     List.iter (fun c ->
         p "noextract\nlet key_%s_%s : asn1_key_lit %s = %s\n\n" n c.cname a.key_term.tk c.clit;
         gitems c.cname c.cfields)
       a.cases;
     Option.iter (gitems "other") a.fallback;
     p "noextract\nlet ls_%s : list (asn1_key_lit %s & asn1_gen_items_lk) = [%s]\n\n" n a.key_term.tk
       (String.concat "; " (List.map (fun c -> sp "(key_%s_%s, gitems_%s_%s)" n c.cname n c.cname) a.cases));
     ilc_consts "(mk_constant_constructed_id 16)"
       (sp "ASN1_ANY_DEFINED_BY _ items_%s %s %s ls_%s %s (_ by (seq_tac ())) (_ by (choice_tac ()))"
          n (idexpr a.key_id) a.key_term.tk n
          (match a.fallback with Some _ -> sp "(Some gitems_%s_other)" n | None -> "None")));
  p "let _ : squash (asn1_k_wf k_%s) = _ by (wf_tac ())\n\n" n

(* Impl types *)

let rec cty ctx (nd: node) = match nd with
  | NRef r -> def_cty ctx r
  | NAny -> slice
  | NILC (_, c) -> ccty ctx c

and ccty ctx (c: cnode) = match c with
  | CTerm (t, _) -> t.cty
  | CRef r -> base_cty ctx r
  | COf (_, _, n) -> sp "(ml %s)" (cty ctx n)
  | CPrefixed n | CContaining n -> cty ctx n

(* The type of `d_r`, with its kept bytes if `r` has KEEP-BYTES *)
and def_cty ctx (r: string) =
  if is_keep ctx r then "t_" ^ r ^ "_kept" else base_cty ctx r

(* The type of `d_r` without KEEP-BYTES at `r`, i.e. that of `cd_r` *)
and base_cty ctx (r: string) = match def ctx r with
  | DStruct (_, []) -> "unit"
  | DStruct _ | DChoice _ | DAdb _ -> "t_" ^ r
  | DNode n -> cty ctx n

let opt_payload ctx (f: field) = match f.fdeco with
  | FPlain -> cty ctx f.fnode
  | FOptional -> cty ctx f.fnode
  | FDefault (_, t, _, _) -> t.cty

let opt_name _ (f: field) = sp "%s_%s" f.fowner f.fname

let field_cty ctx n (f: field) = match f.fdeco with
  | FPlain -> cty ctx f.fnode
  | _ -> "t_" ^ opt_name n f ^ "_opt"

(* Right-nested pairs, the last component unpaired *)
let rec tuple_ty = function
  | [] -> "unit"
  | [t] -> t
  | t :: q -> sp "(%s & %s)" t (tuple_ty q)

let rec either_ty = function
  | [] -> "unit"
  | [t] -> t
  | t :: q -> sp "(either %s %s)" t (either_ty q)

(* Descriptors *)

let rec dexpr (nd: node) = match nd with
  | NRef r -> "d_" ^ r
  | NAny -> "D_ANY"
  | NILC (id, c) -> sp "(D_ILC %s %s)" (idexpr id) (cdexpr c)

and cdexpr (c: cnode) = match c with
  | CTerm (t, None) -> sp "(CD_TERMINAL %s)" t.tk
  | CTerm (t, Some r) -> sp "(CD_RESTRICTED %s %s)" t.tk r
  | CRef r -> "cd_" ^ r
  | COf (set, ne, n) -> sp "(%s %b %s)" (if set then "CD_SET_OF" else "CD_SEQUENCE_OF") ne (dexpr n)
  | CPrefixed n | CContaining n -> sp "(CD_PREFIXED %s)" (dexpr n)

let ddexpr n (f: field) =
  let o = opt_name n f in
  let view d = sp "(DD_VIEW %s t_%s_opt oview_%s omk_%s ())" d o o o in
  match f.fdeco with
  | FPlain -> sp "(DD_PLAIN %s)" (dexpr f.fnode)
  | FOptional -> view (sp "(DD_OPTION %s)" (dexpr f.fnode))
  | FDefault (id, t, None, _) -> view (sp "(DD_DEFAULT %s #%s %s)" (idexpr id) t.tk (dv_name n f))
  | FDefault (id, t, Some r, _) -> view (sp "(DD_DEFAULT_RESTRICTED %s #%s %s %s)" (idexpr id) t.tk r (dv_name n f))

let rec idesc_expr n = function
  | [] -> "ID_NIL"
  | [f] -> sp "(ID_SINGLE %s)" (ddexpr n f)
  | f :: q -> sp "(ID_CONS %s\n      %s)" (ddexpr n f) (idesc_expr n q)

let rec iadesc_expr n = function
  | [] -> "IA_NIL"
  | [f] -> sp "(IA_SINGLE %s)" (ddexpr n f)
  | f :: q -> sp "(IA_CONS %s\n      %s)" (ddexpr n f) (iadesc_expr n q)

(* The i-th injection into `either_ty` of nl types *)
let inj nl i v =
  let rec inrs k e = if k = 0 then e else sp "Inr (%s)" (inrs (k - 1) e) in
  if nl = 1 then v
  else if i = nl - 1 then inrs i v
  else inrs i (sp "Inl %s" v)

(* The i-th component of `tuple_ty` of nf types *)
let access nf i x =
  let rec snds k e = if k = 0 then e else snds (k - 1) (sp "snd (%s)" e) in
  if nf = 1 then x
  else if i = nf - 1 then snds i x
  else sp "fst (%s)" (snds i x)

(* ANY DEFINED BY: the payload of a case (or of the fallback) `s` is a
   named struct `t_<n>_<s>` if it has more than one component *)
let adb_payload ctx n s (fields: field list) =
  match fields with
  | [] | [_] -> tuple_ty (List.map (field_cty ctx n) fields)
  | _ -> sp "t_%s_%s" n s

let adb_key_name (a: adb) = field_name a.key.fname

(* The view of a payload as nested pairs, and back *)
let adb_payload_view n s (fields: field list) v =
  match fields with
  | [] | [_] -> v
  | _ ->
    let rec go = function
      | [] -> "()"
      | [f] -> sp "Mkt_%s_%s?.%s %s" n s (field_name f.fname) v
      | f :: q -> sp "(Mkt_%s_%s?.%s %s, %s)" n s (field_name f.fname) v (go q)
    in go fields

let adb_payload_mk n s (fields: field list) v =
  match fields with
  | [] | [_] -> v
  | _ ->
    let nf = List.length fields in
    sp "(Mkt_%s_%s %s)" n s (String.concat " " (List.mapi (fun i _ -> sp "(%s)" (access nf i v)) fields))

let comment_name ctx n =
  match Hashtbl.find_opt ctx.r.env.user n with
  | Some a -> sp "(* %s *)\n" a
  | None -> sp "(* %s (anonymous) *)\n" n

let gen_opt_types ctx n fields =
    List.iter (fun f -> if f.fdeco <> FPlain then begin
        let o = opt_name n f in
        let pl = opt_payload ctx f in
        p "[@@FStar.Attributes.rename_let \"%s_opt\"]\nnoeq\ntype t_%s_opt =\n| %s_absent : t_%s_opt\n| %s_present : v: %s -> t_%s_opt\n\n" o o o o o pl o;
        p "inline_for_extraction noextract\nlet oview_%s (x: t_%s_opt) : option %s =\n  match x with\n  | %s_absent -> None\n  | %s_present v -> Some v\n\n" o o pl o o;
        p "inline_for_extraction noextract\nlet omk_%s (x: option %s) : t_%s_opt =\n  match x with\n  | None -> %s_absent\n  | Some v -> %s_present v\n\n" o pl o o o
      end) fields

let gen_types ctx (n: string) =
  match def ctx n with
  | DStruct (_, []) -> ()
  | DStruct (_, fields) ->
    gen_opt_types ctx n fields;
    p "%s[@@FStar.Attributes.rename_let \"%s\"]\nnoeq\ntype t_%s = {\n" (comment_name ctx n) n n;
    List.iter (fun f -> p "  %s: %s;\n" (field_name f.fname) (field_cty ctx n f)) fields;
    p "}\n\n"
  | DChoice alts ->
    p "%s[@@FStar.Attributes.rename_let \"%s\"]\nnoeq\ntype t_%s =\n" (comment_name ctx n) n n;
    List.iter (function
        | ALeaf (a, _, c) -> p "| %s_%s : %s: %s -> t_%s\n" n a (field_name a) (ccty ctx c) n
        | ASub (a, r) ->
          if is_keep ctx r then error "KEEP-BYTES is not supported on %s: an untagged alternative of the CHOICE %s" r n;
          p "| %s_%s : %s: t_%s -> t_%s\n" n a (field_name a) r n)
      alts;
    p "\n"
  | DAdb a ->
    gen_opt_types ctx n (adb_fields a);
    let payload s fields =
      match fields with
      | [] | [_] -> ()
      | _ ->
        p "[@@FStar.Attributes.rename_let \"%s_%s\"]\nnoeq\ntype t_%s_%s = {\n" n s n s;
        List.iter (fun f -> p "  %s: %s;\n" (field_name f.fname) (field_cty ctx n f)) fields;
        p "}\n\n"
    in
    List.iter (fun c -> payload c.cname c.cfields) a.cases;
    Option.iter (payload "other") a.fallback;
    let k = a.key.fname in
    p "(* %s.%s, with the components that depend on it *)\n[@@FStar.Attributes.rename_let \"%s_%s\"]\nnoeq\ntype t_%s_%s =\n" n k n k n k;
    List.iter (fun c ->
        p "| %s_%s_%s : %s: %s -> t_%s_%s\n" n k c.cname (field_name c.cname) (adb_payload ctx n c.cname c.cfields) n k)
      a.cases;
    Option.iter (fun fb ->
        p "| %s_%s_other : key: %s -> other: %s -> t_%s_%s\n" n k a.key_term.cty (adb_payload ctx n "other" fb) n k)
      a.fallback;
    p "\n%s[@@FStar.Attributes.rename_let \"%s\"]\nnoeq\ntype t_%s = {\n" (comment_name ctx n) n n;
    List.iter (fun f -> p "  %s: %s;\n" (field_name f.fname) (field_cty ctx n f)) a.prefix;
    p "  %s: t_%s_%s;\n}\n\n" (adb_key_name a) n k
  | DNode _ -> ()

(* The C type `T_kept` of a KEEP-BYTES type `T`: its value and, optionally,
   the bytes of its encoding (set by the parser, ignored by the writers) *)
let gen_kept_types ctx (n: string) =
  if is_keep ctx n then begin
    let b = base_cty ctx n in
    p "[@@FStar.Attributes.rename_let \"%s_raw\"]\nnoeq\ntype t_%s_raw =\n| %s_raw_absent : t_%s_raw\n| %s_raw_present : v: S.slice U8.t -> t_%s_raw\n\n" n n n n n n;
    p "(* %s, with the bytes it was parsed from *)\n[@@FStar.Attributes.rename_let \"%s_kept\"]\nnoeq\ntype t_%s_kept = {\n  value: %s;\n  raw: t_%s_raw;\n}\n\n" n n n b n;
    p "inline_for_extraction noextract\nlet kview_%s (x: t_%s_kept) : kept %s =\n  { kval = x.value; kraw = (match x.raw with | %s_raw_absent -> None | %s_raw_present v -> Some v) }\n\n" n n b n n;
    p "inline_for_extraction noextract\nlet kmk_%s (x: kept %s) : t_%s_kept =\n  { value = x.kval; raw = (match x.kraw with | None -> %s_raw_absent | Some v -> %s_raw_present v) }\n\n" n b n n n
  end

(* The descriptor of a type: `d_T`, or `dbase_T` (wrapped by `d_T`) if `T` has KEEP-BYTES *)
let dname ctx n = if is_keep ctx n then "dbase_" ^ n else "d_" ^ n

let gen_kept_desc ctx (n: string) =
  if is_keep ctx n then begin
    p "noextract\nlet wf_%s : squash (ASN1.Spec.Conformance.wf k_%s) =\n  _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())\n\n" n n;
    p "noextract\nlet d_%s : adesc k_%s t_%s_kept =\n  D_VIEW (D_KEEP dbase_%s wf_%s) t_%s_kept kview_%s kmk_%s ()\n\n" n n n n n n n n
  end

let gen_desc ctx (n: string) =
  match def ctx n with
  | DStruct (set, fields) ->
    let item = if set then sp "CD_SET _ items_%s (ASN1_SET?.pf c_%s)" n n else sp "CD_SEQUENCE gitems_%s" n in
    if fields = [] then
      p "noextract\nlet cd_%s : cdesc c_%s unit = %s ID_NIL\n\n" n n item
    else begin
      let tys = List.map (field_cty ctx n) fields in
      let nf = List.length fields in
      let proj f = sp "Mkt_%s?.%s x" n (field_name f.fname) in
      let rec view = function
        | [] -> "()"
        | [f] -> proj f
        | f :: q -> sp "(%s, %s)" (proj f) (view q)
      in
      let access i =
        let rec snds k e = if k = 0 then e else snds (k - 1) (sp "snd (%s)" e) in
        if nf = 1 then "x"
        else if i = nf - 1 then snds i "x"
        else sp "fst (%s)" (snds i "x")
      in
      p "inline_for_extraction noextract\nlet view_%s (x: t_%s) : %s =\n  %s\n\n" n n (tuple_ty tys) (view fields);
      p "inline_for_extraction noextract\nlet mk_%s (x: %s) : t_%s =\n  Mkt_%s %s\n\n" n (tuple_ty tys) n n
        (String.concat " " (List.mapi (fun i _ -> sp "(%s)" (access i)) fields));
      p "noextract\nlet cd_%s : cdesc c_%s t_%s =\n  CD_VIEW (%s\n      %s)\n    t_%s view_%s mk_%s ()\n\n" n n n item (idesc_expr n fields) n n n
    end;
    p "noextract\nlet %s : adesc k_%s %s = D_ILC id_%s cd_%s\n\n" (dname ctx n) n (base_cty ctx n) n n
  | DChoice _ ->
    let ls = leaves ctx n in
    let nl = List.length ls in
    let tys = List.map (fun (_, _, c) -> ccty ctx c) ls in
    let inj i v =
      let rec inrs k e = if k = 0 then e else sp "Inr (%s)" (inrs (k - 1) e) in
      if nl = 1 then v
      else if i = nl - 1 then inrs i v
      else inrs i (sp "Inl %s" v)
    in
    (* view: match on the constructors, nested for flattened CHOICEs *)
    let counter = ref 0 in
    let rec view_match depth x r =
      let v = sp "v%d" depth in
      let cases = List.map (function
          | ALeaf (a, _, _) -> let i = !counter in incr counter; sp "| %s_%s %s -> %s" r a v (inj i v)
          | ASub (a, r') -> sp "| %s_%s %s -> (%s)" r a v (view_match (depth + 1) v r'))
          (match def ctx r with DChoice alts -> alts | _ -> [])
      in
      sp "match %s with %s" x (String.concat " " cases)
    in
    let wrap path v = List.fold_right (fun c acc -> sp "%s (%s)" c acc) path v in
    let rec mk_match var i = function
      | [] -> "()"
      | [(path, _, _)] -> wrap path var
      | (path, _, _) :: q ->
        let w = sp "w%d" i in
        sp "(match %s with | Inl v -> %s | Inr %s -> %s)" var (wrap path "v") w (mk_match w (i + 1) q)
    in
    let rec lcdesc = function
      | [] -> "LC_NIL"
      | [(_, id, c)] -> sp "(LC_SINGLE %s %s)" (idexpr id) (cdexpr c)
      | (_, id, c) :: q -> sp "(LC_CONS %s %s\n      %s)" (idexpr id) (cdexpr c) (lcdesc q)
    in
    p "inline_for_extraction noextract\nlet view_%s (x: t_%s) : %s =\n  %s\n\n" n n (either_ty tys) (view_match 0 "x" n);
    p "inline_for_extraction noextract\nlet mk_%s (x: %s) : t_%s =\n  %s\n\n" n (either_ty tys) n (mk_match "x" 0 ls);
    p "noextract\nlet %s : adesc k_%s t_%s =\n  D_VIEW (D_CHOICE lc_%s pf_%s\n      %s)\n    t_%s view_%s mk_%s ()\n\n" (dname ctx n) n n n n (lcdesc ls) n n n
  | DAdb a ->
    let k = a.key.fname in
    let cases = List.map (fun c -> (c.cname, c.cfields)) a.cases @ (match a.fallback with Some fb -> [("other", fb)] | None -> []) in
    let nl = List.length cases in
    let tuple fields = tuple_ty (List.map (field_cty ctx n) fields) in
    let fbt fb = sp "(%s & %s)" a.key_term.cty (tuple fb) in
    let ts = either_ty (List.map (fun c -> tuple c.cfields) a.cases @ (match a.fallback with Some fb -> [fbt fb] | None -> [])) in
    let tys = List.map (field_cty ctx n) a.prefix @ [ts] in
    let nf = List.length tys in
    let proj f = sp "Mkt_%s?.%s x" n (field_name f.fname) in
    let suffix_view =
      sp "(match Mkt_%s?.%s x with %s)" n (adb_key_name a)
        (String.concat " " (List.mapi (fun i (s, fields) ->
             if s = "other" && a.fallback <> None && i = nl - 1 then
               sp "| %s_%s_other key v -> %s" n k (inj nl i (sp "(key, %s)" (adb_payload_view n s fields "v")))
             else sp "| %s_%s_%s v -> %s" n k s (inj nl i (sp "(%s)" (adb_payload_view n s fields "v"))))
             cases))
    in
    let rec view = function
      | [] -> suffix_view
      | f :: q -> sp "(%s, %s)" (proj f) (view q)
    in
    let rec mk_suffix var i = function
      | [] -> "()"
      | [(s, fields)] ->
        if s = "other" && a.fallback <> None then
          sp "%s_%s_other (fst %s) %s" n k var (adb_payload_mk n s fields (sp "(snd %s)" var))
        else sp "%s_%s_%s %s" n k s (adb_payload_mk n s fields var)
      | (s, fields) :: q ->
        let w = sp "w%d" i in
        sp "(match %s with | Inl v -> %s_%s_%s %s | Inr %s -> %s)" var n k s (adb_payload_mk n s fields "v") w (mk_suffix w (i + 1) q)
    in
    p "inline_for_extraction noextract\nlet view_%s (x: t_%s) : %s =\n  %s\n\n" n n (tuple_ty tys) (view a.prefix);
    p "inline_for_extraction noextract\nlet mk_%s (x: %s) : t_%s =\n  Mkt_%s %s (%s)\n\n" n (tuple_ty tys) n n
      (String.concat " " (List.mapi (fun i _ -> sp "(%s)" (access nf i "x")) a.prefix))
      (mk_suffix (sp "(%s)" (access nf (nf - 1) "x")) 0 cases);
    let tk = a.key_term.tk in
    let item c = sp "%s key_%s_%s gitems_%s_%s %s" tk n c.cname n c.cname (idesc_expr n c.cfields) in
    let rec sx = function
      | [] -> sp "(SX_NIL %s)" tk
      | [c] -> sp "(SX_SINGLE %s)" (item c)
      | c :: q -> sp "(SX_CONS %s\n      %s)" (item c) (sx q)
    in
    let rec fx = function
      | [] -> sp "(FX_NIL %s)" tk
      | [c] -> sp "(FX_SINGLE %s)" (item c)
      | c :: q -> sp "(FX_CONS %s\n      %s)" (item c) (fx q)
    in
    let adb = match a.fallback with
      | None ->
        sp "CD_ADB_NONE _ items_%s %s %s ls_%s (ASN1_ANY_DEFINED_BY?.pf_wf c_%s) (ASN1_ANY_DEFINED_BY?.pf_sup c_%s)\n      %s\n      %s"
          n (idexpr a.key_id) tk n n n (sx a.cases) (iadesc_expr n a.prefix)
      | Some fb ->
        sp "CD_ADB_SOME _ items_%s %s %s ls_%s gitems_%s_other (ASN1_ANY_DEFINED_BY?.pf_wf c_%s) (ASN1_ANY_DEFINED_BY?.pf_sup c_%s)\n      %s\n      %s\n      %s"
          n (idexpr a.key_id) tk n n n n (idesc_expr n fb) (fx a.cases) (iadesc_expr n a.prefix)
    in
    p "noextract\nlet cd_%s : cdesc c_%s t_%s =\n  CD_VIEW (%s)\n    t_%s view_%s mk_%s ()\n\n" n n n adb n n n;
    p "noextract\nlet %s : adesc k_%s %s = D_ILC id_%s cd_%s\n\n" (dname ctx n) n (base_cty ctx n) n n
  | DNode (NRef r) ->
    if is_ilc ctx r then p "noextract\nlet cd_%s : cdesc c_%s %s = cd_%s\n\n" n n (base_cty ctx r) r;
    p "noextract\nlet %s : adesc k_%s %s = d_%s\n\n" (dname ctx n) n (base_cty ctx n) r
  | DNode NAny ->
    p "noextract\nlet %s : adesc k_%s %s = D_ANY\n\n" (dname ctx n) n slice
  | DNode (NILC (_, c)) ->
    p "noextract\nlet cd_%s : cdesc c_%s %s = %s\n\n" n n (ccty ctx c) (cdexpr c);
    p "noextract\nlet %s : adesc k_%s %s = D_ILC id_%s cd_%s\n\n" (dname ctx n) n (base_cty ctx n) n n

let gen_desc ctx n = gen_desc ctx n; gen_kept_desc ctx n

let norm_attr ns extra =
  sp "normalize_for_extraction [\n  delta_attr [`%%asn1_pulse_attr; `%%ASN1.Pulse.Restrict.asn1_restrict_attr];\n  delta_namespace [\"ASN1.Syntax\"; %s];\n  delta_only [`%%dfst; `%%dsnd; `%%Mkdtuple2?._1; `%%Mkdtuple2?._2; `%%ASN1.Base.k_as_lk; `%%ASN1.Base.list_as_l; `%%ASN1.Base.mk_ASN1_GEN_ITEM; `%%ASN1.Base.proj2_of_3; `%%List.Tot.map;\n    %s];\n  zeta; iota; primops]"
    (String.concat "; " (List.map (sp "%S") ns)) extra

let has_adb ctx = List.exists (fun n -> match def ctx n with DAdb _ -> true | _ -> false) ctx.r.order

let gen_root ctx ns (n: string) =
  let tac = "_ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())" in
  p "noextract\nlet supported_%s : squash (supported_k k_%s) = %s\n\n" n n tac;
  p "noextract\nlet psupported_%s : squash (psupported_k k_%s) = %s\n\n" n n tac;
  p "noextract\nlet ok_%s : squash (RW.raw_ok k_%s) = %s\n\n" n n tac;
  let ty = def_cty ctx n in
  p "(* Check that the input starts with the DER encoding of a %s, and return its size *)\n" n;
  p "[@@%s;\n  FStar.Attributes.rename_let \"validate_%s\"]\n" (norm_attr ns "`%ASN1.Pulse.Interpreter.all_defaultable") n;
  p "let validate_%s : LPS.validator #(asn1_t k_%s) #asn1_strong_parser_kind (asn1_as_parser k_%s) =\n  validate_k k_%s supported_%s\n\n" n n n n n;
  p "(* Read a validated %s (zero-copy: its strings point into the input) *)\n" n;
  p "[@@%s;\n  FStar.Attributes.rename_let \"parse_%s\"]\n" (norm_attr ns ("`%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer" ^
    (if has_adb ctx then "; `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t" else ""))) n;
  p "let parse_%s : aparser #%s #(asn1_t k_%s) (arel true d_%s) #asn1_strong_parser_kind (asn1_as_parser k_%s) =\n  fun input #pm #w #v -> parse_d d_%s psupported_%s input #pm #w #v\n\n" n ty n n n n n;
  p "(* Write a %s right to left, ending at *pos, if it is valid (else\n   JIT_INVALID) and fits (else JIT_NO_SPACE) *)\n" n;
  p "[@@%s;\n  FStar.Attributes.rename_let \"write_%s\"]\n" (norm_attr ns "`%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d") n;
  p "let write_%s : raw_jit_writer_d_t d_%s ok_%s 1.0R =\n  fun x' #y out pos #v #p -> jit_write_raw_d d_%s ok_%s 1.0R (jit_writer_d d_%s ok_%s (1.0R /. 2.0R)) x' #y out pos #v #p\n\n" n n n n n n n;
  p "(* Write a typed %s (related by `arel false d_%s`, e.g. a value returned\n   by parse_%s after ASN1.Pulse.RelKeep.to_writer) that is encodable:\n   never JIT_INVALID *)\n" n n n;
  p "[@@%s;\n  FStar.Attributes.rename_let \"write_%s_typed\"]\n" (norm_attr ns "`%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d") n;
  p "let write_%s_typed : typed_jit_writer_d_t d_%s 1.0R =\n  fun x' #v out pos #b #p -> write_typed_d d_%s ok_%s 1.0R (jit_write_raw_d d_%s ok_%s 1.0R (jit_writer_d d_%s ok_%s (1.0R /. 2.0R))) x' #v out pos #b #p\n\n" n n n n n n n n

(* For a KEEP-BYTES type: hand a parsed value (`arel true`, bytes kept) to
   the writers (`arel false`), and get the parser relation back later *)
let gen_to_writer ctx (n: string) =
  if is_keep ctx n then
    p "ghost fn to_writer_%s (pm: perm) (x: %s) (v: asn1_t k_%s)\nrequires arel true d_%s pm x v\nensures arel false d_%s pm x v ** Trade.trade (arel false d_%s pm x v) (arel true d_%s pm x v)\n{\n  ASN1.Pulse.RelKeep.to_writer d_%s pm x v\n}\n\n" n (def_cty ctx n) n n n n n n

let header src = sp "(* Generated by everparse-asn1 from %s: do not edit *)\n\n" src

let gen_spec_module (r: result) ~src ~spec : string =
  Buffer.clear buf;
  let ctx = { r; spec; keep = [] } in
  p "module %s\n%s" spec (header src);
  p "open ASN1.Base\nopen ASN1.Syntax\n\n";
  p "noextract\nlet mk_gitems (#ids: id_decs) (items: asn1_gen_items_l ids) (_: squash (asn1_sequence_k_wf ids)) : asn1_gen_items_lk =\n  (| ids, items |)\n\n";
  (* The OBJECT IDENTIFIER value assignments *)
  let oids = Hashtbl.fold (fun n (t, _) acc ->
      match t with TBuiltin "OBJECT IDENTIFIER" -> n :: acc | _ -> acc) r.env.values [] in
  List.iter (fun n ->
      let l = oid_value r.env (VName n) in
      p "noextract\nlet oid_%s : asn1_oid_t = mk_oid [%s]\n\n" (mangle n) (String.concat "; " (List.map string_of_int l)))
    (List.sort compare oids);
  List.iter (gen_spec ctx) r.order;
  Buffer.contents buf

let gen_pulse_module (r: result) ~src ~spec ~pulse ~(roots: string list) ~(keep: string list) : string =
  Buffer.clear buf;
  let ctx = { r; spec; keep } in
  p "module %s\n#lang-pulse\n%s" pulse (header src);
  p "open Pulse.Lib.Pervasives\nopen ASN1.Base\nopen ASN1.Spec.Interpreter\nopen ASN1.Pulse.Rel\nopen ASN1.Pulse.Parse\nopen ASN1.Pulse.Interpreter\nopen ASN1.Pulse.Parser\nopen ASN1.Pulse.RawRel\nopen ASN1.Pulse.JitWriter\nopen ASN1.Pulse.RawJitWriter\nopen ASN1.Pulse.TypedWriter\nopen ASN1.Syntax\nopen %s\n" spec;
  p "module S = Pulse.Lib.Slice\nmodule U8 = FStar.UInt8\nmodule I64 = FStar.Int64\nmodule LPS = LowParse.Pulse.Base\nmodule RW = ASN1.Pulse.RawWriter\nmodule Trade = Pulse.Lib.Trade\n\n";
  p "(* C types *)\n\n";
  List.iter (fun n -> gen_types ctx n; gen_kept_types ctx n) r.order;
  p "(* Descriptors *)\n\n";
  List.iter (gen_desc ctx) r.order;
  p "(* Extraction roots *)\n\n";
  List.iter (gen_root ctx [spec; pulse]) roots;
  List.iter (gen_to_writer ctx) r.order;
  Buffer.contents buf
