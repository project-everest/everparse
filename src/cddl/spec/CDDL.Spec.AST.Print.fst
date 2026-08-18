module CDDL.Spec.AST.Print

(* Print an AST value as a string of valid F* syntax. Reparsing the
   output (in a scope where [CDDL.Spec.AST.Base] is in scope) should
   yield a value equal to the original. *)

let escape_char_in_string_literal (c: FStar.Char.char) : Tot (list FStar.Char.char) =
  if c = '\\'
  then ['\\'; '\\']
  else if c = '"'
  then ['\\'; '"']
  else [c]

let rec escape_chars (l: list FStar.Char.char) : Tot (list FStar.Char.char) =
  match l with
  | [] -> []
  | c :: q -> escape_char_in_string_literal c `List.Tot.append` escape_chars q

let print_string_literal (s: string) : Tot string =
  "\"" ^ FStar.String.string_of_list (escape_chars (FStar.String.list_of_string s)) ^ "\""

let print_int_literal (i: int) : Tot string =
  if i < 0
  then "(" ^ string_of_int i ^ ")"
  else string_of_int i

let print_bool (b: bool) : Tot string =
  if b then "true" else "false"

let print_option_int (o: option int) : Tot string =
  match o with
  | None -> "None"
  | Some i -> "(Some " ^ print_int_literal i ^ ")"

let print_literal (l: literal) : Tot string =
  match l with
  | LSimple i -> "(LSimple " ^ print_int_literal i ^ ")"
  | LInt i -> "(LInt " ^ print_int_literal i ^ ")"
  | LTextString s -> "(LTextString " ^ print_string_literal s ^ ")"

let print_elem_typ (e: elem_typ) : Tot string =
  match e with
  | ELiteral l -> "(ELiteral " ^ print_literal l ^ ")"
  | EBool -> "EBool"
  | ESimple -> "ESimple"
  | EByteString -> "EByteString"
  | ETextString -> "ETextString"
  | EUInt -> "EUInt"
  | ENInt -> "ENInt"
  | EAlwaysFalse -> "EAlwaysFalse"
  | EAny -> "EAny"

let rec group_to_string (t: group) : Tot string (decreases t) =
  match t with
  | GDef s -> "(GDef " ^ print_string_literal s ^ ")"
  | GElem cut key value ->
    "(GElem " ^ print_bool cut ^ " " ^ typ_to_string key ^ " " ^ typ_to_string value ^ ")"
  | GAlwaysFalse -> "GAlwaysFalse"
  | GNop -> "GNop"
  | GZeroOrOne g' -> "(GZeroOrOne " ^ group_to_string g' ^ ")"
  | GZeroOrMore g' -> "(GZeroOrMore " ^ group_to_string g' ^ ")"
  | GOneOrMore g' -> "(GOneOrMore " ^ group_to_string g' ^ ")"
  | GConcat g1 g2 -> "(GConcat " ^ group_to_string g1 ^ " " ^ group_to_string g2 ^ ")"
  | GChoice g1 g2 -> "(GChoice " ^ group_to_string g1 ^ " " ^ group_to_string g2 ^ ")"

and typ_to_string (t: typ) : Tot string (decreases t) =
  match t with
  | TElem e -> "(TElem " ^ print_elem_typ e ^ ")"
  | TDef s -> "(TDef " ^ print_string_literal s ^ ")"
  | TArray g -> "(TArray " ^ group_to_string g ^ ")"
  | TMap g -> "(TMap " ^ group_to_string g ^ ")"
  | TNamed name body ->
    "(TNamed " ^ print_string_literal name ^ " " ^ typ_to_string body ^ ")"
  | TTagged tag body ->
    "(TTagged " ^ print_option_int tag ^ " " ^ typ_to_string body ^ ")"
  | TChoice t1 t2 -> "(TChoice " ^ typ_to_string t1 ^ " " ^ typ_to_string t2 ^ ")"
  | TRange t1 inclusive t2 ->
    "(TRange " ^ typ_to_string t1 ^ " " ^ print_bool inclusive ^ " " ^ typ_to_string t2 ^ ")"
  | TSize t1 t2 -> "(TSize " ^ typ_to_string t1 ^ " " ^ typ_to_string t2 ^ ")"
  | TDetCbor t1 t2 -> "(TDetCbor " ^ typ_to_string t1 ^ " " ^ typ_to_string t2 ^ ")"

let print_decl (d: decl) : Tot string =
  match d with
  | DType t -> "(DType " ^ typ_to_string t ^ ")"
  | DGroup g -> "(DGroup " ^ group_to_string g ^ ")"

let print_program_entry (p: (string & decl)) : Tot string =
  "(" ^ print_string_literal (fst p) ^ ", " ^ print_decl (snd p) ^ ")"

let rec print_program_entries (l: list (string & decl)) : Tot string (decreases l) =
  match l with
  | [] -> ""
  | [p] -> print_program_entry p
  | p :: q -> print_program_entry p ^ "; " ^ print_program_entries q

let program_to_string (t: program) : Tot string =
  "[" ^ print_program_entries t ^ "]"
