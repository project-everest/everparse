%{
  open FStar_Pervasives
  open Lexing
  open CDDL_Spec_AST_Base
%}

(* RFC 8610 Appendix B; RFC 9682 *)

%token<string> RAW_ID
%token<string> TEXT
%token NONEMPTY_S
%token EQ "="
%token SLASH "/"
%token LPAREN "("
%token RPAREN ")"
%token LBRACE "{"
%token RBRACE "}"
%token LBRACK "["
%token RBRACK "]"
%token POUND6 "#6"
%token DOT "."
%token POUND "#"
%token<Prims.int> UINT
%token MINUS "-"
%token SLASHSLASH "//"
%token COMMA ","
%token ARROW "=>"
%token COLON ":"
%token HAT "^"
%token STAR "*"
%token PLUS "+"
%token DOLLARDOLLAR "$$"
%token DOLLAR "$"
%token QUESTION "?"
%token EOF

%start <(string * CDDL_Spec_AST_Base.typ) list> cddl

%%

cddl:
  | s l=nonempty_list(cddl_item) EOF { l }

cddl_item:
  | x=rule s { x }

s:
  | NONEMPTY_S s { () }
  | { () }

rule:
  | name=typename (* option(genericparm) *) s f=assignt s t=type_ { f name t }
(* TODO: groupname assigng *)

typename:
  | x=id { (* TODO: check for the environment *) x }

id:
  | x=RAW_ID { x }
(* TODO: "$$", "$" *)

groupname:
  | x=id { (* TODO: check for the environment *) x }

assignt:
  | "=" { (fun (x: string) (t: typ) -> (x, t)) }
(* TODO: /= *)

(* TODO:
assigng:

genericparm:

genericarg:
*)

type_:
  | x=type1 xs=type_tail { xs x }

type_tail:
  | s "/" s xl=type1 xr=type_tail { (fun (x: typ) -> TChoice (x, xr xl)) }
  | { (fun (x: typ) -> x) }

type1:
  | x=type2 (* option(type1_tail) *) { x }

(* TODO
type1_tail:
  | s rangeop_or_ctlop s type2

rangeop_or_ctlop: (* TODO *)
  | rangeop
  | ctlop
*)

type2:
  | x=value { TElem (ELiteral x) }
  | x=typename (* option(genericarg) *) { TDef x }
  | "(" s x=type_ s ")" { x }
  | "{" s x=group s "}" { TMap x }
  | "[" s x=group s "]" { TArray x }
(* TODO: "~" s typename option(genericarg) *)
(* TODO: "&" s "(" s group s ")" *)
(* TODO: "&" s groupname option(genericarg) *)
  | "#6" tag=option(tag) "(" s x=type_ s ")" { TTagged (tag, x) }
(* TODO: "#"DIGIT option(tag) *)
  | "#" { TElem EAny }

tag:
  | "." x=UINT { x }

(* TODO
rangeop:

ctlop:
*)

group:
  | a=grpchoice q=group_tail { q a }

group_tail:
  | s "//" s a=grpchoice q=group_tail { (fun (x: group) -> GChoice (x, q a)) }
  | { (fun (x: group) -> x) }

grpchoice:
  | a=grpent optcom q=grpchoice { GConcat (a, q) }
  | { GNop }

grpent:
  | f=option_occur g=option_memberkey x=type_ { f (g x) }
  | f=option_occur g=groupname (* option(genericarg) *) { f (GDef g) }
  | f=option_occur "(" s g=group s ")" { f g }

option_memberkey:
  | f=memberkey { f }
  | { (fun x -> GElem (false, TElem EAny, x)) }

memberkey:
  | key=type1 s cut=memberkey_cut "=>" { (fun x -> GElem (cut, key, x)) }
  | key=bareword s ":" { (fun x -> GElem (true, TElem (ELiteral (LString (KTextString, key))), x)) }
  | key=value s ":" { (fun x -> (GElem (true, TElem (ELiteral key), x))) }

memberkey_cut:
  | "^" s { true }
  | { false }

bareword:
  | x=id { x }

optcom:
  | s option(optcom_tail) { () }

optcom_tail:
  | "," s { () }

occur:
(* TODO: bounds *)
  | "+" { (fun x -> GOneOrMore x) }
  | "?" { (fun x -> GZeroOrOne x) }
  | (* option(occur_from) *) "*" (* option(occur_to) *) { (fun x -> GZeroOrMore x) }

option_occur:
  | { (fun (x: group) -> x) }
  | f=occur { f }

value:
  | x=number { LInt x }
  | x=TEXT { LString (KTextString, x) }

number:
(* TODO: hexfloat *)
  | x=int { x }
(* TODO: floats *)

int:
  | x=UINT { x }
  | "-" x=UINT { Prims.( ~- ) x }
