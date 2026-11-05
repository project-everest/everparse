(* Abstract syntax of the supported subset of ASN.1 (X.680) *)

type tag_class = Universal | Application | Context | Private

type tag_mode = TImplicit | TExplicit | TDefault

type tag_default = DExplicit | DImplicit | DAutomatic

type value =
  | VInt of int
  | VBool of bool
  | VName of string          (* a named number or a value reference *)

type bound = Min | Max | Val of int

type constr =
  | CSize of constr                    (* SIZE (...) *)
  | CRange of bound * bound            (* lo .. hi *)
  | CSingle of int list                (* v1 | v2 | ... *)

type typ =
  | TBuiltin of string                 (* BOOLEAN, NULL, OCTET STRING, ... *)
  | TInteger of (string * int) list    (* named numbers *)
  | TEnumerated of (string * int option) list
  | TBitString                         (* named bits are ignored *)
  | TAny
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

type modul = {
  mname: string;
  tag_default: tag_default;
  assignments: assignment list;
}

exception Error of string

let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt
