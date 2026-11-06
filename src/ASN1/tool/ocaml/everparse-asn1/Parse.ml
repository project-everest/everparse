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

let value st = match peek st with
  | NUM _ | MINUS -> VInt (number st)
  | ID "TRUE" -> advance st; VBool true
  | ID "FALSE" -> advance st; VBool false
  | ID s when is_lower s -> advance st; VName s
  | LBRACE -> oid_value st
  | _ -> fail st "unsupported value (only INTEGER, BOOLEAN, OBJECT IDENTIFIER and named values are supported)"

let bound st = match peek st with
  | ID "MIN" -> advance st; Min
  | ID "MAX" -> advance st; Max
  | ID s when is_lower s -> advance st; BRef s
  | _ -> Val (number st)

(* The contents of ( ... ): SIZE (c), lo..hi, v1 | v2 | ..., or CONTAINING T *)
let rec constr_body st =
  match peek st with
  | ID "SIZE" -> advance st; expect st LPAREN; let c = constr_body st in expect st RPAREN; CSize c
  | ID "CONTAINING" ->
    advance st;
    let t = typ st in
    if peek st = ID "ENCODED" then fail st "ENCODED BY is not supported";
    CContaining t
  | ELLIPSIS -> fail st "extensible constraints are not supported"
  | _ ->
    let lo = bound st in
    if peek st = DOTDOT then begin
      advance st;
      if peek st = LT then fail st "open ranges (<) are not supported";
      let hi = bound st in
      if peek st = COMMA || peek st = BAR then fail st "unions of ranges are not supported";
      CRange (lo, hi)
    end else begin
      let v = function Min | Max -> fail st "MIN/MAX outside of a range" | b -> b in
      let rec more acc = if peek st = BAR then (advance st; more (v (bound st) :: acc)) else List.rev acc in
      let vs = more [v lo] in
      if peek st = COMMA then fail st "extensible constraints are not supported";
      CSingle vs
    end

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
    | "BIT" -> expect_kw st "STRING"; if peek st = LBRACE then skip_braces st; TBitString
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
    | "EXTERNAL" | "EMBEDDED" | "CHARACTER" | "REAL" | "INSTANCE" | "TYPE-IDENTIFIER" ->
      fail st "type %s is not supported" s
    | _ when is_upper s ->
      if peek st = DOT || peek st = LBRACE then fail st "external references and parameterized types are not supported";
      TRef s
    | _ -> fail st "expected a type"
    end
  | _ -> fail st "expected a type"

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

let assignment st =
  let n = ident st in
  if is_upper n then begin
    expect st ASSIGN; TypeAssign (n, typ st)
  end else begin
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
            if peek st = LBRACE then fail st "parameterized imports are not supported";
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
   --#KEEP-BYTES T1 T2 ...
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
        | ID s when is_upper s -> advance st; names (s :: keep)
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
          let v = value st in
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

let parse_file (file: string) : modul =
  let ic = open_in_bin file in
  let lexbuf = Lexing.from_channel ic in
  Lexer.line := 1;
  Lexer.directives := [];
  let toks =
    try lex_all lexbuf
    with Lexer.Lex_error s -> close_in ic; error "%s" s
  in
  close_in ic;
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
