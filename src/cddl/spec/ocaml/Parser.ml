open ABNF
open Tokens
open FStar_Pervasives
open CDDL_Spec_AST_Base

type state = unit
type 'a parser = (token, state, 'a) ABNF.parser
type symbol = unit parser

let terminal name f =
  terminal (fun x ->
      print_spaces ();
      print_endline ("Entering terminal " ^ name ^ " with token " ^ show_token x);
      let res = f x in
      print_spaces ();
      begin match res with
      | Some _ -> print_endline ("Success: " ^ name)
      | _ -> print_endline ("Failure: " ^ name)
      end;
      res
    )

let raw_id : string parser = terminal "raw_id" (function RAW_ID s -> Some s | _ -> None)
let text = terminal "text" (function TEXT s -> Some s | _ -> None)
let uint = terminal "uint" (function UINT s -> Some s | _ -> None)
let nonempty_s = terminal "nonempty_s" (function NONEMPTY_S -> Some () | _ -> None)
let eq = terminal "eq" (function EQ -> Some () | _ -> None)
let slash = terminal "slash" (function SLASH -> Some () | _ -> None)
let lparen = terminal "lparen" (function LPAREN -> Some () | _ -> None)
let rparen = terminal "rparen" (function RPAREN -> Some () | _ -> None)
let lbrace = terminal "lbrace" (function LBRACE -> Some () | _ -> None)
let rbrace = terminal "rbrace" (function RBRACE -> Some () | _ -> None)
let lbrack = terminal "lbrack" (function LBRACK -> Some () | _ -> None)
let rbrack = terminal "rbrack" (function RBRACK -> Some () | _ -> None)
let pound0 = terminal "pound0" (function POUND0 -> Some () | _ -> None)
let pound1 = terminal "pound1" (function POUND1 -> Some () | _ -> None)
let pound2 = terminal "pound2" (function POUND2 -> Some () | _ -> None)
let pound3 = terminal "pound3" (function POUND3 -> Some () | _ -> None)
let pound6 = terminal "pound6" (function POUND6 -> Some () | _ -> None)
let pound7 = terminal "pound7" (function POUND7 -> Some () | _ -> None)
let dot = terminal "dot" (function DOT -> Some () | _ -> None)
let pound = terminal "pound"  (function POUND -> Some () | _ -> None)
let minus = terminal "minus" (function MINUS -> Some () | _ -> None)
let slashslash = terminal "slashslash" (function SLASHSLASH -> Some () | _ -> None)
let comma = terminal "comma" (function COMMA -> Some () | _ -> None)
let arrow = terminal "arrow" (function ARROW -> Some () | _ -> None)
let colon = terminal "colon" (function COLON -> Some () | _ -> None)
let hat = terminal "hat" (function HAT -> Some () | _ -> None)
let star = terminal "star" (function STAR -> Some () | _ -> None)
let plus = terminal "plus" (function PLUS -> Some () | _ -> None)
let dollardollar : symbol = terminal "dollardollar" (function DOLLARDOLLAR -> Some () | _ -> None)
let dollar : symbol = terminal "dollar" (function DOLLAR -> Some () | _ -> None)
let question = terminal "question" (function QUESTION -> Some () | _ -> None)
let eof = terminal "eof" (function EOF -> Some () | _ -> None)

let s = debug "s" (choice (nonempty_s) (ret ()))

let id = debug "id" raw_id (* TODO: "$$", "$" *)

let typename = debug "typename" id (* TODO: check for the environment *)

let groupname = debug "groupname" id (* TODO: check for the environment *)

let assignt = debug "assignt" (concat eq (fun _ -> ret (fun (x: string) (t: typ) -> (x, CDDL_Spec_AST_Driver.DType t))))

(* TODO: /= *)

let assigng = debug "assigng" (concat eq (fun _ -> ret (fun (x: string) (t: group) -> (x, CDDL_Spec_AST_Driver.DGroup t))))

(* TODO: //= *)

(* TODO:

genericparm:

genericarg:
*)

let int = debug "int" (
  choice
    uint
    (concat minus (fun _ -> concat uint (fun x -> ret (Prims.( ~- ) x))))
)

let number = debug "number" int
(* TODO: hexfloat *)
(* TODO: floats *)

let value = debug "value" (
  choice
    (concat number (fun x -> ret (LInt x)))
    (concat text (fun x -> ret (LString (KTextString, x))))
)

let tag = debug "tag" (concat dot (fun _ -> uint))

let memberkey_cut = debug "memberkey_cut" (
  choice
    (concat hat (fun _ -> ret true))
    (ret false)
)

let bareword = debug "bareword" id

let occur = debug "occur" (
  choices
    [
      concat plus (fun _ -> ret (fun x -> GOneOrMore x));
      concat question (fun _ -> ret (fun x -> GZeroOrOne x));
(* TODO: bounds *)
      concat (* option(occur_from) *) star (* option(occur_to) *) (fun _ -> ret (fun x -> GZeroOrMore x));
    ]
)

let option_occur = debug "option_occur" (
  choice
    (concat occur (fun x -> concat s (fun _ -> ret x)))
    (ret (fun (x: group) -> x))
)

let optcom = debug "optcom" (concat s (fun _ -> option (concat comma (fun _ -> s))))

let rec type_ () = debug "type" (
  concat (type1 ()) (fun x -> concat (type_tail ()) (fun xs -> ret (xs x)))
)

and type_tail () = debug "type_tail" (
  choice
    (concat s (fun _ -> concat slash (fun _ -> concat s (fun _ -> concat (type1 ()) (fun xl -> concat (type_tail ()) (fun xr -> ret (fun (x: typ) -> TChoice (x, xr xl))))))))
    (ret (fun (x: typ) -> x))
)

and type1 () = debug "type1" (type2 ()) (* option(type1_tail) *) 

(* TODO
type1_tail:
  | s rangeop_or_ctlop s type2

rangeop_or_ctlop: (* TODO *)
  | rangeop
  | ctlop
*)

and type2 () = debug "type2" (
  choices
    [
      concat value (fun x -> ret (TElem (ELiteral x)));
      concat typename (fun x -> (* option(genericarg) *) ret (TDef x));
      concat lparen (fun _ -> concat s (fun _ -> concat (type_ ()) (fun x -> concat s (fun _ -> concat rparen (fun _ -> ret x)))));
      concat lbrace (fun _ -> concat s (fun _ -> concat (group ()) (fun x -> concat s (fun _ -> concat rbrace (fun _ -> ret (TMap x))))));
      concat lbrack (fun _ -> concat s (fun _ -> concat (group ()) (fun x -> concat s (fun _ -> concat rbrack (fun _ -> ret (TArray x))))));
(* TODO: "~" s typename option(genericarg) *)
(* TODO: "&" s "(" s group s ")" *)
(* TODO: "&" s groupname option(genericarg) *)
      concat pound6 (fun _ -> concat (option tag) (fun tag -> concat lparen (fun _ -> concat s (fun _ -> concat (type_ ()) (fun x -> concat s (fun _ -> concat rparen (fun _ -> ret (TTagged (tag, x)))))))));
(* TODO: generalize "#"DIGIT option(tag) *)
      concat pound0 (fun _ -> ret (TElem EUInt));
      concat pound1 (fun _ -> ret (TElem ENInt));
      concat pound2 (fun _ -> ret (TElem EByteString));
      concat pound3 (fun _ -> ret (TElem ETextString));
      concat pound7 (fun _ -> concat (option tag) (fun tag -> ret (match tag with None -> TElem ESimple | Some v -> TElem (ELiteral (LSimple v)))));
      concat pound (fun _ -> ret (TElem EAny));
    ]
)

and group () = debug "group" (
  concat (grpchoice ()) (fun a -> concat (group_tail ()) (fun q -> ret (q a)))
)

and group_tail () = debug "group_tail" (
  choice
    (concat s (fun _ -> concat slashslash (fun _ -> concat s (fun _ -> concat (grpchoice ()) (fun a -> concat (group_tail ()) (fun q -> ret (fun (x: group) -> GChoice (x, q a))))))))
    (ret (fun (x: group) -> x))
)

and grpchoice () = debug "grpchoice" (
  choice
    (concat (grpent ()) (fun a -> concat optcom (fun _ -> concat (grpchoice ()) (fun q -> ret (GConcat (a, q))))))
    (ret GNop)
)

and grpent () = debug "grpent" (
  choices
    [
      concat option_occur (fun f -> concat (option_memberkey ()) (fun g -> concat (type_ ()) (fun x -> ret (f (g x)))));
      concat option_occur (fun f -> concat groupname (* option(genericarg) *) (fun g -> ret (f (GDef g))));
      concat option_occur (fun f -> concat lparen (fun _ -> concat s (fun _ -> concat (group ()) (fun g -> concat s (fun _ -> concat rparen (fun _ -> ret (f g)))))));
    ]
)

and option_memberkey () = debug "option_memberkey" (
  choice
    (concat (memberkey ()) (fun x -> concat s (fun _ -> ret x)))
    (ret (fun x -> GElem (false, TElem EAny, x)))
)

and memberkey () = debug "memberkey" (
  choices
    [
      concat (type1 ()) (fun key -> concat s (fun _ -> concat memberkey_cut (fun cut -> concat arrow (fun _ -> ret (fun x -> GElem (cut, key, x))))));
      concat bareword (fun key -> concat s (fun _ -> concat colon (fun _ -> ret (fun x -> GElem (true, TElem (ELiteral (LString (KTextString, key))), x)))));
      concat value (fun key -> concat s (fun _ -> concat colon (fun _ -> ret (fun x -> (GElem (true, TElem (ELiteral key), x))))));
    ]
)

let rec cddl () : ((string * CDDL_Spec_AST_Driver.decl) list) parser = debug_start "cddl" (
  concat s (fun _ -> concat (nonempty_list (cddl_item ())) (fun l -> concat eof (fun _ -> ret (List.rev l))))
)

and cddl_item () : ((string * CDDL_Spec_AST_Driver.decl)) parser = debug "cddl_item" (
  concat (rule ()) (fun x -> concat s (fun _ -> ret x))
)

and rule () : ((string * CDDL_Spec_AST_Driver.decl)) parser =
  debug "rule"
    (choice
       (concat typename (* option(genericparm) *) (fun name -> concat s (fun _ -> concat assignt (fun f -> concat s (fun _ -> concat (type_ ()) (fun t -> ret (f name t)))))))
       (concat groupname (* option(genericparm) *) (fun name -> concat s (fun _ -> concat assigng (fun f -> concat s (fun _ -> concat (group ()) (fun t -> ret (f name t)))))))
    )
