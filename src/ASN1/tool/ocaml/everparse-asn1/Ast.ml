(* Abstract syntax of the supported subset of ASN.1 (X.680) *)

type tag_class = Universal | Application | Context | Private

type tag_mode = TImplicit | TExplicit | TDefault

type tag_default = DExplicit | DImplicit | DAutomatic

type value =
  | VInt of int
  | VBool of bool
  | VName of string          (* a named number or a value reference *)
  | VOid of oid_comp list    (* { iso(1) member-body(2) 840 } or { id-ce 19 } *)

and oid_comp =
  | ONum of int              (* 840 *)
  | OName of string          (* id-ce: an OBJECT IDENTIFIER value (first component only) *)
  | ONamed of string * int   (* iso(1) *)

type bound = Min | Max | Val of int | BRef of string (* an INTEGER value reference *)

type constr =
  | CSize of constr                    (* SIZE (...) *)
  | CRange of bound * bound            (* lo .. hi *)
  | CSingle of bound list              (* v1 | v2 | ... *)
  | CContaining of typ                 (* CONTAINING T (X.682 11) *)

and typ =
  | TBuiltin of string                 (* BOOLEAN, NULL, OCTET STRING, ... *)
  | TInteger of (string * int) list    (* named numbers *)
  | TEnumerated of (string * int option) list
  | TBitString                         (* named bits are ignored *)
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

and component =
  | Field of string * typ * deco
  | ComponentsOf of typ

and deco = DPlain | DOptional | DDefault of value

type assignment =
  | TypeAssign of string * typ
  | ValueAssign of string * typ * value

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
