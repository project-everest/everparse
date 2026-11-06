(* Recursive-descent parser for the supported subset of ASN.1 (X.680) *)

open Ast
open Lexer

type st = { toks: (token * int) array; mutable pos: int }

let peek st = fst st.toks.(st.pos)
let peek2 st = if st.pos + 1 < Array.length st.toks then fst st.toks.(st.pos + 1) else EOF
let line st = snd st.toks.(st.pos)
let advance st = if st.pos < Array.length st.toks - 1 then st.pos <- st.pos + 1

let show = function
  | ID s -> s | NUM n -> string_of_int n | ASSIGN -> "::=" | LBRACE -> "{"
  | RBRACE -> "}" | LPAREN -> "(" | RPAREN -> ")" | LBRACKET -> "["
  | RBRACKET -> "]" | COMMA -> "," | DOTDOT -> ".." | ELLIPSIS -> "..."
  | BAR -> "|" | MINUS -> "-" | SEMI -> ";" | DOT -> "." | LT -> "<" | COLON -> ":"
  | CSTRING s -> "\"" ^ s ^ "\"" | BSTRING s -> "'" ^ s ^ "'B" | HSTRING s -> "'" ^ s ^ "'H"
  | AMP s -> "&" ^ s | AT -> "@" | CARET -> "^"
  | EOF -> "end of file"

let fail st fmt =
  Printf.ksprintf (fun s -> error "line %d: %s (at '%s')" (line st) s (show (peek st))) fmt

let expect st t =
  if peek st = t then advance st else fail st "expected '%s'" (show t)

let kw st k = if peek st = ID k then (advance st; true) else false
let expect_kw st k = if not (kw st k) then fail st "expected '%s'" k

let is_upper s = s <> "" && Char.uppercase_ascii s.[0] = s.[0] && Char.lowercase_ascii s.[0] <> s.[0]
let is_lower s = s <> "" && not (is_upper s)

let ident st = match peek st with ID s -> advance st; s | _ -> fail st "expected an identifier"

let lower_ident st = match peek st with
  | ID s when is_lower s -> advance st; s
  | _ -> fail st "expected an identifier starting with a lowercase letter"

let number st = match peek st with
  | NUM n -> advance st; n
  | MINUS -> advance st; (match peek st with NUM n -> advance st; -n | _ -> fail st "expected a number")
  | _ -> fail st "expected a number"

(* Skip a balanced { ... } (module OIDs) *)
let rec skip_braces st =
  expect st LBRACE;
  let rec go () = match peek st with
    | RBRACE -> advance st
    | LBRACE -> skip_braces st; go ()
    | EOF -> fail st "unbalanced braces"
    | _ -> advance st; go ()
  in go ()

(* The tokens of a balanced { ... }, without the outer braces *)
let raw_braces st : raw =
  let start = line st in
  expect st LBRACE;
  let rec go depth acc =
    let (t, _) as x = st.toks.(st.pos) in
    match t with
    | EOF -> error "line %d: unbalanced braces" start
    | RBRACE when depth = 0 -> advance st; List.rev acc
    | RBRACE -> advance st; go (depth - 1) (x :: acc)
    | LBRACE -> advance st; go (depth + 1) (x :: acc)
    | _ -> advance st; go depth (x :: acc)
  in go 0 []

(* X.681 7.1: the names of classes are in uppercase *)
let is_class_name s =
  String.exists (fun c -> 'A' <= c && c <= 'Z') s &&
  String.for_all (fun c -> ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c = '-') s

let builtin_type_words = ["BOOLEAN"; "NULL"; "INTEGER"; "ENUMERATED"; "BIT"; "OCTET"; "OBJECT";
                          "ANY"; "SEQUENCE"; "SET"; "CHOICE"; "EXTERNAL"; "EMBEDDED"; "CHARACTER";
                          "REAL"; "DATE"; "TIME-OF-DAY"; "DATE-TIME"; "RELATIVE-OID"; "OID-IRI";
                          "RELATIVE-OID-IRI"; "INSTANCE"]

(* An object set { o1 | o2 | { inline } | Set, ... }: references and
   inline objects, with | or UNION, and an extension marker *)
let obj_set st : obj_set =
  expect st LBRACE;
  let rec go elems ext =
    match peek st with
    | RBRACE -> advance st; { elems = List.rev elems; ext }
    | ELLIPSIS -> advance st; go elems true
    | COMMA | BAR | ID "UNION" -> advance st; go elems ext
    | ID s when is_lower s -> advance st; go (EObject s :: elems) ext
    | ID s ->
      advance st;
      if peek st = LBRACE then fail st "parameterized object sets are not supported";
      go (ESet s :: elems) ext
    | LBRACE -> let r = raw_braces st in go (EInline r :: elems) ext
    | _ -> fail st "unsupported object set element"
  in go [] false

(* An OBJECT IDENTIFIER value: { iso(1) member-body(2) 840 } or { id-ce 19 } *)
let oid_value st =
  expect st LBRACE;
  let rec go acc =
    match peek st with
    | RBRACE -> advance st; List.rev acc
    | NUM n -> advance st; go (ONum n :: acc)
    | ID s when is_lower s ->
      advance st;
      if peek st = LPAREN then begin
        advance st;
        let n = match peek st with NUM n -> advance st; n | _ -> fail st "expected a number" in
        expect st RPAREN; go (ONamed (s, n) :: acc)
      end else go (OName s :: acc)
    | _ -> fail st "unsupported OBJECT IDENTIFIER component"
  in
  match go [] with
  | [] -> fail st "empty OBJECT IDENTIFIER value"
  | l -> VOid l

(* Named bits { a, b } (X.680 22.9); { } is empty and { a } is parsed as an OBJECT IDENTIFIER *)
let bits_value st =
  expect st LBRACE;
  if peek st = RBRACE then (advance st; VBits [])
  else
    let rec go acc =
      let acc = lower_ident st :: acc in
      if peek st = COMMA then (advance st; go acc) else (expect st RBRACE; VBits (List.rev acc))
    in go []

(* A comma-separated list of the items `item`, up to the closing brace *)
let brace_list st item =
  expect st LBRACE;
  let rec go acc =
    let acc = item st :: acc in
    if peek st = COMMA then (advance st; go acc) else (expect st RBRACE; List.rev acc)
  in go []

(* `colon`: whether `name : value` is a CHOICE value (not in the cases of
   a DEFINED-BY directive) *)
let rec value ?(colon = true) st = match peek st with
  | NUM _ | MINUS -> VInt (number st)
  | ID "TRUE" -> advance st; VBool true
  | ID "FALSE" -> advance st; VBool false
  | ID "NULL" -> advance st; VNull
  | ID s when is_lower s && colon && peek2 st = COLON ->
    advance st; advance st; ignore (value st); VOpaque "a CHOICE value"
  | ID s when is_lower s -> advance st; VName s
  | CSTRING s -> advance st; VCString s
  | BSTRING s -> advance st; VBString s
  | HSTRING s -> advance st; VHString s
  | LBRACE -> brace_value st
  | _ -> fail st "unsupported value (only INTEGER, BOOLEAN, NULL, OBJECT IDENTIFIER, string, bit string, named and constructed values are supported)"

(* { ... }: named bits, an OBJECT IDENTIFIER, a Quadruple or Tuple, a
   CharacterStringList, or else a constructed value (SEQUENCE, SET,
   SEQUENCE OF, ...), which is skipped *)
and brace_value st =
  let save = st.pos in
  let attempt f = try Some (f st) with Error _ -> st.pos <- save; None in
  let char_item st = match peek st with
    | CSTRING s -> advance st; VCString s
    | ID s when is_lower s -> advance st; VName s
    | LBRACE -> VNumList (brace_list st number)
    | _ -> fail st "expected a character string"
  in
  let alternatives = [
    (fun st -> match peek2 st, fst st.toks.(min (st.pos + 2) (Array.length st.toks - 1)) with
       | RBRACE, _ | ID _, COMMA -> bits_value st
       | _ -> fail st "not named bits");
    oid_value;
    (fun st -> VNumList (brace_list st number));
    (fun st -> VCharList (brace_list st char_item));
  ] in
  match List.find_map attempt alternatives with
  | Some v -> v
  | None -> skip_braces st; VOpaque "a constructed value"

let bound st = match peek st with
  | ID "MIN" -> advance st; Min
  | ID "TRUE" -> advance st; BBool true
  | ID "FALSE" -> advance st; BBool false
  | ID "MAX" -> advance st; Max
  | ID s when is_lower s -> advance st; BRef s
  | _ -> Val (number st)

(* The contents of ( ... ): SIZE (c), a union of ranges lo..hi (with lo<
   or <hi for an excluded endpoint) and values v1 | v2 | ..., CONTAINING T,
   or WITH COMPONENT(S) *)
let rec constr_body st =
  match peek st with
  | ID "CONTAINING" ->
    advance st;
    let t = typ st in
    if peek st = ID "ENCODED" then fail st "ENCODED BY is not supported";
    CContaining t
  | ID "WITH" ->
    advance st;
    if kw st "COMPONENTS" then begin
      expect st LBRACE;
      let partial = peek st = ELLIPSIS in
      if partial then begin
        advance st;
        if peek st = COMMA then advance st
      end;
      let rec items acc =
        if peek st = RBRACE then (advance st; List.rev acc) else begin
          let n = lower_ident st in
          let c = if peek st = LPAREN then Some (constr st) else None in
          let p =
            if kw st "PRESENT" then Some PPresent
            else if kw st "ABSENT" then Some PAbsent
            else if kw st "OPTIONAL" then Some POptional
            else None
          in
          let acc = (n, c, p) :: acc in
          if peek st = COMMA then (advance st; items acc) else (expect st RBRACE; List.rev acc)
        end
      in
      CWithComponents (partial, items [])
    end else begin
      expect_kw st "COMPONENT";
      CWithComponent (constr st)
    end
  | ELLIPSIS -> fail st "extensible constraints are not supported"
  | LBRACE ->
    (* a table constraint {Set} or {Set}{@key} *)
    let set = obj_set st in
    let key =
      if peek st = LBRACE then begin
        advance st;
        expect st AT;
        if peek st = DOT then fail st "relative component references (@.c) are not supported";
        let k = lower_ident st in
        if peek st = DOT then fail st "component references of nested components (@a.b) are not supported";
        if peek st = COMMA then fail st "table constraints with several keys are not supported";
        expect st RBRACE;
        Some k
      end else None
    in
    CTable (set, key)
  | _ ->
    let c = element_set st in
    if peek st = COMMA then fail st "extensible constraints are not supported";
    c

(* X.680 50: ALL EXCEPT e | e1 UNION e2 ^ e3 EXCEPT e4 ..., with the
   precedence EXCEPT > INTERSECTION > UNION *)
and element_set st =
  if kw st "ALL" then (expect_kw st "EXCEPT"; CAll (elements st))
  else begin
    let rec go acc =
      if peek st = BAR || peek st = ID "UNION" then (advance st; go (intersections st :: acc)) else List.rev acc in
    match go [intersections st] with
    | [e] -> e
    | es when List.for_all (function CSingle _ -> true | _ -> false) es ->
      CSingle (List.concat_map (function CSingle l -> l | _ -> []) es)
    | es -> CUnion es
  end

and intersections st =
  let elems () = let e = elements st in if kw st "EXCEPT" then CExcept (e, elements st) else e in
  let rec go acc =
    if peek st = CARET || peek st = ID "INTERSECTION" then (advance st; go (elems () :: acc)) else List.rev acc in
  match go [elems ()] with
  | [e] -> e
  | es -> CInter es

and elements st =
  match peek st with
  | LPAREN -> advance st; let c = element_set st in expect st RPAREN; c
  | ID "SIZE" -> advance st; expect st LPAREN; let c = element_set st in expect st RPAREN; CSize c
  | ID ("FROM" | "PATTERN" | "INCLUDES" as k) -> fail st "%s constraints are not supported" k
  | ID ("CONTAINING" | "WITH") | LBRACE -> fail st "this constraint is not supported in a set operation"
  | _ ->
    let lo = bound st in
    let lo = if peek st = LT then (advance st; Open lo) else lo in
    if peek st = DOTDOT then begin
      advance st;
      let hi = if peek st = LT then (advance st; Open (bound st)) else bound st in
      CRange (lo, hi)
    end else match lo with
      | Min | Max -> fail st "MIN/MAX outside of a range"
      | Open _ -> fail st "expected '..'"
      | b -> CSingle [b]

and constr st = expect st LPAREN; let c = constr_body st in expect st RPAREN; c

and typ st =
  let t = base_typ st in
  let rec post t =
    if peek st = LPAREN then post (TConstrained (t, constr st)) else t
  in post t

and base_typ st =
  match peek st with
  | LBRACKET ->
    advance st;
    let cls = match peek st with
      | ID "UNIVERSAL" -> advance st; Universal
      | ID "APPLICATION" -> advance st; Application
      | ID "PRIVATE" -> advance st; Private
      | _ -> Context
    in
    let n = number st in
    if n < 0 then fail st "negative tag number";
    expect st RBRACKET;
    let mode = if kw st "IMPLICIT" then TImplicit else if kw st "EXPLICIT" then TExplicit else TDefault in
    TTagged (cls, n, mode, typ st)
  | ID s ->
    advance st;
    begin match s with
    | "BOOLEAN" | "NULL" | "ObjectDescriptor" | "UTF8String" | "PrintableString"
    | "IA5String" | "VisibleString" | "ISO646String" | "BMPString" | "UniversalString"
    | "TeletexString" | "T61String" | "NumericString" | "VideotexString"
    | "GraphicString" | "GeneralString" | "UTCTime" | "GeneralizedTime" | "DATE"
    | "TIME-OF-DAY" | "DATE-TIME" | "RELATIVE-OID" | "OID-IRI" | "RELATIVE-OID-IRI" ->
      TBuiltin s
    | "INTEGER" ->
      if peek st = LBRACE then begin
        advance st;
        let rec items acc =
          let n = lower_ident st in
          expect st LPAREN; let v = number st in expect st RPAREN;
          let acc = (n, v) :: acc in
          if peek st = COMMA then (advance st; items acc) else (expect st RBRACE; List.rev acc)
        in TInteger (items [])
      end else TInteger []
    | "ENUMERATED" ->
      expect st LBRACE;
      let rec items acc =
        if peek st = ELLIPSIS then fail st "extensible ENUMERATED is not supported";
        let n = lower_ident st in
        let v = if peek st = LPAREN then (advance st; let v = number st in expect st RPAREN; Some v) else None in
        let acc = (n, v) :: acc in
        if peek st = COMMA then (advance st; items acc) else (expect st RBRACE; List.rev acc)
      in TEnumerated (items [])
    | "BIT" ->
      expect_kw st "STRING";
      if peek st = LBRACE then begin
        advance st;
        let rec items acc =
          let n = lower_ident st in
          expect st LPAREN; let v = number st in expect st RPAREN;
          if v < 0 then fail st "negative bit number";
          let acc = (n, v) :: acc in
          if peek st = COMMA then (advance st; items acc) else (expect st RBRACE; List.rev acc)
        in TBitString (items [])
      end else TBitString []
    | "OCTET" -> expect_kw st "STRING"; TBuiltin "OCTET STRING"
    | "OBJECT" -> expect_kw st "IDENTIFIER"; TBuiltin "OBJECT IDENTIFIER"
    | "ANY" ->
      if kw st "DEFINED" then (expect_kw st "BY"; TAnyDefinedBy (lower_ident st))
      else TAny
    | "SEQUENCE" | "SET" ->
      let set = s = "SET" in
      begin match peek st with
      | LBRACE -> let cs = components st in if set then TSet cs else TSequence cs
      | _ ->
        let c =
          if peek st = ID "SIZE" then (advance st; Some (CSize (constr st)))
          else if peek st = LPAREN then Some (constr st)
          else None
        in
        expect_kw st "OF";
        (* SEQUENCE OF name Type *)
        (match peek st, peek2 st with
         | ID n, (ID _ | LBRACKET) when is_lower n -> advance st
         | _ -> ());
        let t = typ st in
        if set then TSetOf (c, t) else TSequenceOf (c, t)
      end
    | "CHOICE" ->
      expect st LBRACE;
      let rec alts acc =
        if peek st = ELLIPSIS then fail st "extensible CHOICE is not supported";
        let n = lower_ident st in
        let t = typ st in
        let acc = (n, t) :: acc in
        if peek st = COMMA then (advance st; alts acc) else (expect st RBRACE; List.rev acc)
      in TChoice (alts [])
    (* The universal types of the prelude (Prelude.ml) *)
    | "EXTERNAL" -> TRef "EXTERNAL"
    | "EMBEDDED" -> expect_kw st "PDV"; TRef "EMBEDDED-PDV"
    | "CHARACTER" -> expect_kw st "STRING"; TRef "CHARACTER-STRING"
    | ("TYPE-IDENTIFIER" | "ABSTRACT-SYNTAX") when peek st = DOT ->
      advance st;
      (match peek st with AMP f -> advance st; TField (s, f) | _ -> fail st "expected a field (&name)")
    | "REAL" | "INSTANCE" | "TYPE-IDENTIFIER" | "ABSTRACT-SYNTAX" ->
      fail st "type %s is not supported" s
    | _ when is_upper s && peek st = DOT && (match peek2 st with AMP _ -> true | _ -> false) ->
      advance st;
      (match peek st with AMP f -> advance st; if peek st = DOT then fail st "nested field references are not supported"; TField (s, f) | _ -> assert false)
    | _ when is_upper s ->
      if peek st = DOT then fail st "external references are not supported";
      if peek st = LBRACE then TInst (s, args st) else TRef s
    | _ -> fail st "expected a type"
    end
  | _ -> fail st "expected a type"

(* The actual parameters { T, 5, ... } of a parameterized type: types start
   with an uppercase letter or a tag *)
and args st =
  expect st LBRACE;
  let rec go acc =
    let a = match peek st, peek2 st with
      | LBRACE, ID s when is_upper s -> ASet (obj_set st)
      | ID s, _ when is_upper s -> AType (typ st)
      | LBRACKET, _ -> AType (typ st)
      | _ -> AValue (value ~colon:false st)
    in
    let acc = a :: acc in
    if peek st = COMMA then (advance st; go acc) else (expect st RBRACE; List.rev acc)
  in go []

and components st =
  expect st LBRACE;
  if peek st = RBRACE then (advance st; [])
  else
    let rec go acc =
      if peek st = ELLIPSIS then fail st "extensible SEQUENCE/SET is not supported";
      let c =
        if peek st = ID "COMPONENTS" then begin
          advance st; expect_kw st "OF"; ComponentsOf (typ st)
        end else begin
          let n = lower_ident st in
          let t = typ st in
          let d =
            if kw st "OPTIONAL" then DOptional
            else if kw st "DEFAULT" then DDefault (value st)
            else DPlain
          in Field (n, t, d)
        end
      in
      let acc = c :: acc in
      if peek st = COMMA then (advance st; go acc) else (expect st RBRACE; List.rev acc)
    in go []

(* The formal parameters { T, INTEGER : ub, ... } of a parameterized type *)
let params st =
  expect st LBRACE;
  let rec go acc =
    let p = match peek st, peek2 st with
      | ID s, (COMMA | RBRACE) when is_upper s -> advance st; PType s
      | _ ->
        let gov = typ st in
        expect st COLON;
        match peek st, gov with
        | ID s, _ when is_lower s -> advance st; PValue (gov, s)
        | ID s, TRef c when is_class_name c -> advance st; PSet (c, s)
        | _ -> fail st "only type, value and object set parameters are supported"
    in
    let acc = p :: acc in
    if peek st = COMMA then (advance st; go acc) else (expect st RBRACE; List.rev acc)
  in go []

(* Skip to the next , or } at depth 0; were OPTIONAL or DEFAULT seen? *)
let skip_field st =
  let opt = ref false in
  let rec go depth =
    match peek st with
    | (COMMA | RBRACE) when depth = 0 -> ()
    | LBRACE | LPAREN | LBRACKET -> advance st; go (depth + 1)
    | RBRACE | RPAREN | RBRACKET -> advance st; go (depth - 1)
    | ID ("OPTIONAL" | "DEFAULT") when depth = 0 -> opt := true; advance st; go depth
    | EOF -> fail st "unexpected end of file"
    | _ -> advance st; go depth
  in go 0; !opt

(* CLASS { &field ..., ... } [WITH SYNTAX { ... }] *)
let class_def st : class_def =
  expect_kw st "CLASS";
  expect st LBRACE;
  let rec fields acc =
    let f = match peek st with
      | AMP n ->
        advance st;
        if is_upper n then begin
          match peek st with
          | COMMA | RBRACE -> FsType (n, false)
          | ID ("OPTIONAL" | "DEFAULT") -> FsType (n, skip_field st)
          | _ -> ignore (skip_field st); FsOther n
        end else begin
          match peek st with
          | AMP _ -> ignore (skip_field st); FsOther n
          | _ ->
            let save = st.pos in
            match (try Some (typ st) with Error _ -> None) with
            | Some t ->
              ignore (kw st "UNIQUE");
              FsValue (n, t, skip_field st)
            | None -> st.pos <- save; ignore (skip_field st); FsOther n
        end
      | _ -> fail st "expected a field (&name)"
    in
    let acc = f :: acc in
    if peek st = COMMA then (advance st; fields acc) else (expect st RBRACE; List.rev acc)
  in
  let cl_fields = fields [] in
  let cl_syntax =
    if kw st "WITH" then begin
      expect_kw st "SYNTAX";
      expect st LBRACE;
      let rec items close acc =
        if peek st = close then (advance st; List.rev acc) else
        let it = match peek st with
          | LBRACKET -> advance st; SOpt (items RBRACKET [])
          | AMP f -> advance st; SField f
          | ID w -> advance st; SWord w
          | COMMA -> advance st; SWord ","
          | _ -> fail st "unsupported WITH SYNTAX item"
        in
        items close (it :: acc)
      in
      Some (items RBRACE [])
    end else None
  in
  { cl_fields; cl_syntax }

(* The settings of the fields of an object (X.681 11) *)
type setting = SetType of typ | SetValue of value | SetOther

let parse_object (cls: class_def) (r: raw) : (string * setting) list =
  let last = match List.rev r with (_, l) :: _ -> l | [] -> 0 in
  let st = { toks = Array.of_list (r @ [(EOF, last)]); pos = 0 } in
  let kind f =
    match List.find_opt (function FsType (n, _) | FsValue (n, _, _) | FsOther n -> n = f) cls.cl_fields with
    | Some k -> k
    | None -> fail st "the class has no field &%s" f
  in
  let setting f =
    match kind f with
    | FsType _ -> SetType (typ st)
    | FsValue _ -> SetValue (value ~colon:false st)
    | FsOther _ ->
      (match peek st with
       | LBRACE -> skip_braces st
       | ID s when is_upper s -> ignore (typ st)
       | _ -> ignore (value ~colon:false st));
      SetOther
  in
  match cls.cl_syntax with
  | None ->
    (* the default syntax: &field setting, ... *)
    let rec go acc =
      match peek st with
      | EOF -> List.rev acc
      | AMP f ->
        advance st;
        let s = setting f in
        let acc = (f, s) :: acc in
        if peek st = COMMA then advance st else if peek st <> EOF then fail st "expected ','";
        go acc
      | _ -> fail st "expected a field (&name)"
    in go []
  | Some syntax ->
    let acc = ref [] in
    let rec items l = List.iter item l
    and item = function
      | SWord "," -> expect st COMMA
      | SWord w -> expect_kw st w
      | SField f -> let s = setting f in acc := (f, s) :: !acc
      | SOpt l ->
        (* an optional group: taken if it matches (greedy) *)
        let save = st.pos and saved = !acc in
        (try items l with Error _ -> st.pos <- save; acc := saved)
    in
    items syntax;
    if peek st <> EOF then fail st "the object does not follow the syntax of its class";
    List.rev !acc

(* A value given as tokens (an ObjectAssign that turns out to be a value) *)
let parse_value (r: raw) : value =
  let last = match List.rev r with (_, l) :: _ -> l | [] -> 0 in
  let st = { toks = Array.of_list ((LBRACE, last) :: r @ [(RBRACE, last); (EOF, last)]); pos = 0 } in
  let v = value ~colon:false st in
  if peek st <> EOF then fail st "trailing tokens";
  v

let assignment st =
  let n = ident st in
  if is_upper n then begin
    if peek st = LBRACE then begin
      let ps = params st in
      expect st ASSIGN; TypeTemplate (n, ps, typ st)
    end else match peek st with
      | ID c when peek2 st = ASSIGN ->
        (* Name CLASS ::= { ... }: an object set *)
        advance st; advance st;
        if not (is_class_name c) || List.mem c builtin_type_words then fail st "value sets are not supported";
        ObjectSetAssign (n, c, obj_set st)
      | _ ->
        expect st ASSIGN;
        match peek st, peek2 st with
        | ID "CLASS", _ -> ClassAssign (n, class_def st)
        | ID ("TYPE-IDENTIFIER" | "ABSTRACT-SYNTAX" as c), t when t <> DOT -> advance st; ClassAlias (n, c)
        | _ -> TypeAssign (n, typ st)
  end else begin
    if peek st = LBRACE then fail st "parameterized values are not supported";
    match peek st, peek2 st with
    | ID c, ASSIGN when is_class_name c && not (List.mem c builtin_type_words) ->
      (* name CLASS ::= { ... }: an object (or a value of an uppercase type) *)
      advance st; advance st;
      if peek st = LBRACE then ObjectAssign (n, c, raw_braces st)
      else ValueAssign (n, TRef c, value st)
    | _ ->
    let t = typ st in expect st ASSIGN; ValueAssign (n, t, value st)
  end

let modul st =
  let mname = ident st in
  if peek st = LBRACE then skip_braces st;
  expect_kw st "DEFINITIONS";
  let tag_default =
    if kw st "EXPLICIT" then (expect_kw st "TAGS"; DExplicit)
    else if kw st "IMPLICIT" then (expect_kw st "TAGS"; DImplicit)
    else if kw st "AUTOMATIC" then (expect_kw st "TAGS"; DAutomatic)
    else DExplicit
  in
  if peek st = ID "EXTENSIBILITY" then fail st "EXTENSIBILITY IMPLIED is not supported";
  expect st ASSIGN;
  expect_kw st "BEGIN";
  if kw st "EXPORTS" then begin
    while peek st <> SEMI && peek st <> EOF do advance st done; expect st SEMI
  end;
  let imports =
    if kw st "IMPORTS" then begin
      (* IMPORTS a, B FROM M1 {oid} c FROM M2 ; *)
      let rec go acc =
        if peek st = SEMI then (advance st; List.rev acc)
        else begin
          let rec syms acc =
            let s = ident st in
            if peek st = LBRACE then (advance st; expect st RBRACE);  (* a parameterized type: Name{} *)
            let acc = s :: acc in
            if peek st = COMMA then (advance st; syms acc) else List.rev acc
          in
          let ss = syms [] in
          expect_kw st "FROM";
          let m = ident st in
          (match peek st, peek2 st with
           | LBRACE, _ -> skip_braces st
           | ID v, t when is_lower v && t <> COMMA && t <> ID "FROM" -> advance st (* an assigned identifier *)
           | _ -> ());
          go ((m, ss) :: acc)
        end
      in go []
    end else []
  in
  let rec go acc =
    if kw st "END" then List.rev acc else go (assignment st :: acc)
  in
  let assignments = go [] in
  if peek st <> EOF then fail st "trailing input after END";
  { mname; tag_default; imports; assignments; directives = []; keep_bytes = [] }

(* The `--#` directives:
   --#KEEP-BYTES T1 T2.component ...
   --#DEFINED-BY Type.field [BY key] { value : body, ... } [FALLBACK (NONE | body)]
   where body is ABSENT, CONTAINING T, or T [OPTIONAL] *)
let directives st : defined_by list * string list =
  let body st =
    if kw st "ABSENT" then BAbsent
    else if kw st "CONTAINING" then BContaining (typ st)
    else let t = typ st in BType (t, kw st "OPTIONAL")
  in
  let rec go dbs keep =
    match peek st with
    | EOF -> List.rev dbs, List.rev keep
    | ID "KEEP-BYTES" ->
      advance st;
      let rec names keep = match peek st with
        | COMMA -> advance st; names keep
        | ID ("KEEP-BYTES" | "DEFINED-BY") -> keep
        | ID s when is_upper s ->
          advance st;
          if peek st = DOT then (advance st; let c = lower_ident st in names ((s ^ "." ^ c) :: keep))
          else names (s :: keep)
        | _ -> keep
      in go dbs (names keep)
    | ID "DEFINED-BY" ->
      let db_line = line st in
      advance st;
      let db_type = ident st in
      expect st DOT;
      let db_field = lower_ident st in
      let db_key = if kw st "BY" then Some (lower_ident st) else None in
      expect st LBRACE;
      let rec cases acc =
        if peek st = RBRACE then (advance st; List.rev acc)
        else begin
          let v = value ~colon:false st in
          expect st COLON;
          let b = body st in
          let acc = (v, b) :: acc in
          if peek st = COMMA then (advance st; cases acc) else (expect st RBRACE; List.rev acc)
        end
      in
      let db_cases = cases [] in
      let db_fallback =
        if kw st "FALLBACK" then (if kw st "NONE" then FbNone else FbBody (body st))
        else FbDeclared
      in
      go ({ db_type; db_field; db_key; db_cases; db_fallback; db_line } :: dbs) keep
    | _ -> fail st "unknown directive (expected KEEP-BYTES or DEFINED-BY)"
  in go [] []

let lex_all lexbuf =
  let rec go acc =
    let t = Lexer.token lexbuf in
    let l = !Lexer.line in
    if t = EOF then List.rev acc else go ((t, l) :: acc)
  in go []

let parse_lexbuf (lexbuf: Lexing.lexbuf) : modul =
  Lexer.line := 1;
  Lexer.directives := [];
  let toks =
    try lex_all lexbuf
    with Lexer.Lex_error s -> error "%s" s
  in
  let last = !Lexer.line in
  let m = modul { toks = Array.of_list (toks @ [(EOF, last)]); pos = 0 } in
  let dtoks =
    try
      List.concat_map (fun (l, text) ->
          Lexer.line := l;
          lex_all (Lexing.from_string text))
        (List.rev !Lexer.directives)
    with Lexer.Lex_error s -> error "in a --# directive: %s" s
  in
  let directives, keep_bytes = directives { toks = Array.of_list (dtoks @ [(EOF, last)]); pos = 0 } in
  { m with directives; keep_bytes }

let parse_file (file: string) : modul =
  let ic = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () -> parse_lexbuf (Lexing.from_channel ic))

let parse_string (text: string) : modul = parse_lexbuf (Lexing.from_string text)
