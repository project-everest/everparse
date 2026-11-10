(* Abstract syntax of the supported subset of ASN.1 (X.680) *)

type tag_class = Universal | Application | Context | Private

type tag_mode = TImplicit | TExplicit | TDefault

type tag_default = DExplicit | DImplicit | DAutomatic

type value =
  | VInt of int
  | VBool of bool
  | VName of string          (* a named number or a value reference *)
  | VOid of oid_comp list    (* { iso(1) member-body(2) 840 } or { id-ce 19 } *)
  | VCString of string       (* "text" *)
  | VBString of string       (* '0101'B: the binary digits *)
  | VHString of string       (* '0A1F'H: the hexadecimal digits *)
  | VNull                    (* NULL *)
  | VBits of string list     (* { bit1, bit2 }: named bits ({ bit1 } parses as VOid) *)
  | VNumList of int list     (* { 1, 2, 3, 4 }: a Quadruple or a Tuple (X.680 41.8) *)
  | VCharList of value list  (* { "abc", ref, {0, 0, 1, 2} }: a CharacterStringList (X.680 41.8) *)
  | VOpaque of string        (* a value that is parsed but not supported: SEQUENCE, CHOICE, ... values *)

and oid_comp =
  | ONum of int              (* 840 *)
  | OName of string          (* id-ce: an OBJECT IDENTIFIER value (first component only) *)
  | ONamed of string * int   (* iso(1) *)

type bound =
  | Min | Max | Val of int
  | BRef of string                     (* an INTEGER or BOOLEAN value reference *)
  | BBool of bool                      (* TRUE, FALSE *)
  | Open of bound                      (* an excluded endpoint: lo<.. or ..<hi *)

(* Information objects (X.681) are kept as tokens, until the syntax of
   their class is known *)
type raw = (Lexer.token * int) list

type set_elem =
  | EObject of string                  (* an object reference *)
  | EInline of raw                     (* { ... }: an object *)
  | ESet of string                     (* an object set reference *)

type obj_set = { elems: set_elem list; ext: bool (* extensible: has ... *) }

type constr =
  | CSize of constr                    (* SIZE (...) *)
  | CRange of bound * bound            (* lo .. hi *)
  | CSingle of bound list              (* v1 | v2 | ... *)
  | CUnion of constr list              (* unions (| or UNION) *)
  | CInter of constr list              (* intersections (^ or INTERSECTION), and serial constraints T (C1) (C2) *)
  | CExcept of constr * constr         (* C1 EXCEPT C2 *)
  | CAll of constr                     (* ALL EXCEPT C *)
  | CContaining of typ                 (* CONTAINING T (X.682 11) *)
  | CWithComponent of constr           (* WITH COMPONENT (c): on the elements of a SEQUENCE OF / SET OF *)
  | CWithComponents of bool * (string * constr option * presence option) list
                                       (* WITH COMPONENTS { [..., ] name [(c)] [PRESENT|ABSENT|OPTIONAL], ... }:
                                          partial?, component constraints (X.680 51.8) *)

  | CTable of obj_set * string option  (* ({Set}) or ({Set}{@key}): a table constraint (X.682 10); the key
                                          as written: a, a.b (absolute), .a, ..a (relative) *)
  | CIncludes of typ                   (* INCLUDES T, or T: a contained subtype (X.680 51.3) *)

and presence = PPresent | PAbsent | POptional

and typ =
  | TBuiltin of string                 (* BOOLEAN, NULL, OCTET STRING, ... *)
  | TInteger of (string * int) list    (* named numbers *)
  | TEnumerated of (string * int option) list
  | TBitString of (string * int) list  (* named bits *)
  | TAny
  | TAnyDefinedBy of string            (* ANY DEFINED BY component *)
  | TRef of string
  | TSequence of component list
  | TSet of component list
  | TSequenceOf of constr option * typ
  | TSetOf of constr option * typ
  | TChoice of (string * typ) list
  | TTagged of tag_class * int * tag_mode * typ
  | TConstrained of typ * constr
  | TInst of string * arg list         (* an instance of a parameterized type: Name { T, 5 } *)
  | TField of string * string          (* CLASS.&field *)

and arg =
  | AType of typ
  | AValue of value
  | ASet of obj_set                    (* {Set}: an object set *)

and component =
  | Field of string * typ * deco
  | ComponentsOf of typ

and deco = DPlain | DOptional | DDefault of value

(* The formal parameters of a parameterized type (X.683) *)
type param =
  | PType of string                    (* T *)
  | PValue of typ * string             (* INTEGER : ub *)
  | PSet of string * string            (* CLASS : Set *)

(* Information object classes (X.681 9) *)
type field_spec =
  | FsType of string * bool            (* &Type [OPTIONAL | DEFAULT T]: optional? *)
  | FsValue of string * typ * bool     (* &id T [UNIQUE] [OPTIONAL | DEFAULT v]: optional? *)
  | FsOther of string                  (* other fields (value sets, objects, ...): ignored *)

type syntax_item =                     (* WITH SYNTAX (X.681 10) *)
  | SWord of string                    (* a word, or "," *)
  | SField of string                   (* &field *)
  | SOpt of syntax_item list           (* [ ... ] *)

type class_def = { cl_fields: field_spec list; cl_syntax: syntax_item list option }

type assignment =
  | TypeAssign of string * typ
  | ValueAssign of string * typ * value
  | TypeTemplate of string * param list * typ  (* Name { params } ::= T *)
  | ClassAssign of string * class_def          (* NAME ::= CLASS { ... } *)
  | ClassAlias of string * string              (* NAME ::= OTHER-CLASS *)
  | ObjectAssign of string * string * raw      (* name CLASS ::= { ... } *)
  | ObjectSetAssign of string * string * obj_set  (* Name CLASS ::= { ... } *)

(* A `--#DEFINED-BY Type.field [BY key] { key : body, ... } [FALLBACK body]`
   directive: the cases of an ANY DEFINED BY (or of any component that
   depends on an earlier key component) *)
type case_body =
  | BAbsent                            (* ABSENT: no component *)
  | BType of typ * bool                (* a type, OPTIONAL? *)
  | BContaining of typ                 (* CONTAINING T: the declared type, containing T *)

type fallback =
  | FbDeclared                         (* the declared component (default) *)
  | FbNone                             (* NONE: unknown keys are rejected *)
  | FbBody of case_body

type defined_by = {
  db_type: string;
  db_field: string;
  db_key: string option;               (* BY key; default: that of ANY DEFINED BY *)
  db_cases: (value * case_body) list;
  db_fallback: fallback;
  db_line: int;
}

type modul = {
  mname: string;
  tag_default: tag_default;
  imports: (string * string list) list;  (* module, symbols *)
  assignments: assignment list;
  directives: defined_by list;
  keep_bytes: string list;
}

exception Error of string

let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt
