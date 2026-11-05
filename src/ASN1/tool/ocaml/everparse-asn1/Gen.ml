(* Generation of the F* modules:
   - `M.fst`: the schema, as `ASN1.Base` terms (`k_T` for each type `T`);
   - `M.Pulse.fst`: a named C type for each SEQUENCE, SET, CHOICE and
     OPTIONAL/DEFAULT component, the impl descriptors (`d_T`) that map them
     to the schema, and the extraction roots `validate_T`, `parse_T` and
     `write_T` for each root type `T`. *)

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

let cls_name = function
  | Universal -> "UNIVERSAL" | Application -> "APPLICATION"
  | Context -> "CONTEXT_SPECIFIC" | Private -> "PRIVATE"

let idexpr (id: id) =
  match id.cls with
  | Universal ->
    if id.num = 0 then error "[UNIVERSAL 0] is not a valid tag";
    sp "(%s %d)" (if id.cons then "mk_constant_constructed_id" else "mk_constant_id") id.num
  | c -> sp "(mk_custom_id %s %s %d)" (cls_name c) (if id.cons then "CONSTRUCTED" else "PRIMITIVE") id.num

type ctx = { r: result; spec: string (* the spec module name *) }

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
  | CPrefixed n -> sp "(ASN1_PREFIXED %s)" (kexpr n)

(* The default value of a DEFAULT component, defined in the spec module *)
let dv_name n (f: field) = sp "dv_%s_%s" n f.fname

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
   | DNode (NILC (id, c)) -> ilc_consts (idexpr id) (cexpr c));
  p "let _ : squash (asn1_k_wf k_%s) = _ by (wf_tac ())\n\n" n

(* Impl types *)

let rec cty ctx (nd: node) = match nd with
  | NRef r -> def_cty ctx r
  | NAny -> slice
  | NILC (_, c) -> ccty ctx c

and ccty ctx (c: cnode) = match c with
  | CTerm (t, _) -> t.cty
  | CRef r -> def_cty ctx r
  | COf (_, _, n) -> sp "(ml %s)" (cty ctx n)
  | CPrefixed n -> cty ctx n

and def_cty ctx (r: string) = match def ctx r with
  | DStruct (_, []) -> "unit"
  | DStruct _ | DChoice _ -> "t_" ^ r
  | DNode n -> cty ctx n

let opt_payload ctx (f: field) = match f.fdeco with
  | FPlain -> cty ctx f.fnode
  | FOptional -> cty ctx f.fnode
  | FDefault (_, t, _, _) -> t.cty

let opt_name n (f: field) = sp "%s_%s" n f.fname

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
  | CPrefixed n -> sp "(CD_PREFIXED %s)" (dexpr n)

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

let comment_name ctx n =
  match Hashtbl.find_opt ctx.r.env.user n with
  | Some a -> sp "(* %s *)\n" a
  | None -> sp "(* %s (anonymous) *)\n" n

let gen_types ctx (n: string) =
  match def ctx n with
  | DStruct (_, []) -> ()
  | DStruct (_, fields) ->
    List.iter (fun f -> if f.fdeco <> FPlain then begin
        let o = opt_name n f in
        let pl = opt_payload ctx f in
        p "[@@FStar.Attributes.rename_let \"%s_opt\"]\nnoeq\ntype t_%s_opt =\n| %s_absent : t_%s_opt\n| %s_present : v: %s -> t_%s_opt\n\n" o o o o o pl o;
        p "inline_for_extraction noextract\nlet oview_%s (x: t_%s_opt) : option %s =\n  match x with\n  | %s_absent -> None\n  | %s_present v -> Some v\n\n" o o pl o o;
        p "inline_for_extraction noextract\nlet omk_%s (x: option %s) : t_%s_opt =\n  match x with\n  | None -> %s_absent\n  | Some v -> %s_present v\n\n" o pl o o o
      end) fields;
    p "%s[@@FStar.Attributes.rename_let \"%s\"]\nnoeq\ntype t_%s = {\n" (comment_name ctx n) n n;
    List.iter (fun f -> p "  %s: %s;\n" (field_name f.fname) (field_cty ctx n f)) fields;
    p "}\n\n"
  | DChoice alts ->
    p "%s[@@FStar.Attributes.rename_let \"%s\"]\nnoeq\ntype t_%s =\n" (comment_name ctx n) n n;
    List.iter (function
        | ALeaf (a, _, c) -> p "| %s_%s : %s: %s -> t_%s\n" n a (field_name a) (ccty ctx c) n
        | ASub (a, r) -> p "| %s_%s : %s: t_%s -> t_%s\n" n a (field_name a) r n)
      alts;
    p "\n"
  | DNode _ -> ()

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
    p "noextract\nlet d_%s : adesc k_%s %s = D_ILC id_%s cd_%s\n\n" n n (def_cty ctx n) n n
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
    p "noextract\nlet d_%s : adesc k_%s t_%s =\n  D_VIEW (D_CHOICE lc_%s pf_%s\n      %s)\n    t_%s view_%s mk_%s ()\n\n" n n n n n (lcdesc ls) n n n
  | DNode (NRef r) ->
    if is_ilc ctx r then p "noextract\nlet cd_%s : cdesc c_%s %s = cd_%s\n\n" n n (def_cty ctx n) r;
    p "noextract\nlet d_%s : adesc k_%s %s = d_%s\n\n" n n (def_cty ctx n) r
  | DNode NAny ->
    p "noextract\nlet d_%s : adesc k_%s %s = D_ANY\n\n" n n slice
  | DNode (NILC (_, c)) ->
    p "noextract\nlet cd_%s : cdesc c_%s %s = %s\n\n" n n (ccty ctx c) (cdexpr c);
    p "noextract\nlet d_%s : adesc k_%s %s = D_ILC id_%s cd_%s\n\n" n n (def_cty ctx n) n n

let norm_attr ns extra =
  sp "normalize_for_extraction [\n  delta_attr [`%%asn1_pulse_attr; `%%ASN1.Pulse.Restrict.asn1_restrict_attr];\n  delta_namespace [\"ASN1.Syntax\"; %s];\n  delta_only [`%%dfst; `%%dsnd; `%%Mkdtuple2?._1; `%%Mkdtuple2?._2; `%%ASN1.Base.k_as_lk; `%%ASN1.Base.list_as_l; `%%ASN1.Base.mk_ASN1_GEN_ITEM; `%%ASN1.Base.proj2_of_3; `%%List.Tot.map;\n    %s];\n  zeta; iota; primops]"
    (String.concat "; " (List.map (sp "%S") ns)) extra

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
  p "[@@%s;\n  FStar.Attributes.rename_let \"parse_%s\"]\n" (norm_attr ns "`%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer") n;
  p "let parse_%s : aparser #%s #(asn1_t k_%s) (arel d_%s) #asn1_strong_parser_kind (asn1_as_parser k_%s) =\n  fun input #pm #w #v -> parse_d d_%s psupported_%s input #pm #w #v\n\n" n ty n n n n n;
  p "(* Write a %s right to left, ending at *pos, if it is valid (else\n   JIT_INVALID) and fits (else JIT_NO_SPACE) *)\n" n;
  p "[@@%s;\n  FStar.Attributes.rename_let \"write_%s\"]\n" (norm_attr ns "`%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d") n;
  p "let write_%s : raw_jit_writer_d_t d_%s ok_%s 1.0R =\n  fun x' #y out pos #v #p -> jit_write_raw_d d_%s ok_%s 1.0R (jit_writer_d d_%s ok_%s 1.0R) x' #y out pos #v #p\n\n" n n n n n n n

let header src = sp "(* Generated by everparse-asn1 from %s: do not edit *)\n\n" src

let gen_spec_module (r: result) ~src ~spec : string =
  Buffer.clear buf;
  let ctx = { r; spec } in
  p "module %s\n%s" spec (header src);
  p "open ASN1.Base\nopen ASN1.Syntax\n\n";
  p "noextract\nlet mk_gitems (#ids: id_decs) (items: asn1_gen_items_l ids) (_: squash (asn1_sequence_k_wf ids)) : asn1_gen_items_lk =\n  (| ids, items |)\n\n";
  List.iter (gen_spec ctx) r.order;
  Buffer.contents buf

let gen_pulse_module (r: result) ~src ~spec ~pulse ~(roots: string list) : string =
  Buffer.clear buf;
  let ctx = { r; spec } in
  p "module %s\n#lang-pulse\n%s" pulse (header src);
  p "open Pulse.Lib.Pervasives\nopen ASN1.Base\nopen ASN1.Spec.Interpreter\nopen ASN1.Pulse.Rel\nopen ASN1.Pulse.Parse\nopen ASN1.Pulse.Interpreter\nopen ASN1.Pulse.Parser\nopen ASN1.Pulse.RawRel\nopen ASN1.Pulse.JitWriter\nopen ASN1.Pulse.RawJitWriter\nopen ASN1.Syntax\nopen %s\n" spec;
  p "module S = Pulse.Lib.Slice\nmodule U8 = FStar.UInt8\nmodule I64 = FStar.Int64\nmodule LPS = LowParse.Pulse.Base\nmodule RW = ASN1.Pulse.RawWriter\n\n";
  p "(* C types *)\n\n";
  List.iter (gen_types ctx) r.order;
  p "(* Descriptors *)\n\n";
  List.iter (gen_desc ctx) r.order;
  p "(* Extraction roots *)\n\n";
  List.iter (gen_root ctx [spec; pulse]) roots;
  Buffer.contents buf
