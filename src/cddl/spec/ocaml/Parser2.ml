open ABNF
open Tokens
open FStar_Pervasives
open CDDL_Spec_AST_Base

let raw_id = terminal (function RAW_ID s -> Some s | _ -> None)
let text = terminal (function TEXT s -> Some s | _ -> None)
let uint = terminal (function UINT s -> Some s | _ -> None)
let nonempty_s = terminal (function NONEMPTY_S -> Some () | _ -> None)
let eq = terminal (function EQ -> Some () | _ -> None)
let slash = terminal (function SLASH -> Some () | _ -> None)
let lparen = terminal (function LPAREN -> Some () | _ -> None)
let rparen = terminal (function RPAREN -> Some () | _ -> None)
let lbrace = terminal (function LBRACE -> Some () | _ -> None)
let rbrace = terminal (function RBRACE -> Some () | _ -> None)
let lbrack = terminal (function LBRACK -> Some () | _ -> None)
let rbrack = terminal (function RBRACK -> Some () | _ -> None)
let pound6 = terminal (function POUND6 -> Some () | _ -> None)
let dot = terminal (function DOT -> Some () | _ -> None)
let pound = terminal (function POUND -> Some () | _ -> None)
let minus = terminal (function MINUS -> Some () | _ -> None)
let slashslash = terminal (function SLASHSLASH -> Some () | _ -> None)
let comma = terminal (function COMMA -> Some () | _ -> None)
let arrow = terminal (function ARROW -> Some () | _ -> None)
let colon = terminal (function COLON -> Some () | _ -> None)
let hat = terminal (function HAT -> Some () | _ -> None)
let star = terminal (function STAR -> Some () | _ -> None)
let plus = terminal (function PLUS -> Some () | _ -> None)
let dollardollar = terminal (function DOLLARDOLLAR -> Some () | _ -> None)
let dollar = terminal (function DOLLAR -> Some () | _ -> None)
let question = terminal (function QUESTION -> Some () | _ -> None)
let eof = terminal (function EOF -> Some () | _ -> None)

let s = choice (ignore_list nonempty_s) (ret ())

let id = raw_id (* TODO: "$$", "$" *)

let typename = id (* TODO: check for the environment *)

let groupname = id (* TODO: check for the environment *)

let assignt = concat eq (fun _ -> ret (fun (x: string) (t: typ) -> (x, t)))

(* TODO: /= *)

(* TODO:
assigng:

genericparm:

genericarg:
*)

let int =
  choice
    uint
    (concat minus (fun _ -> concat uint (fun x -> ret (Prims.( ~- ) x))))

let number = int
(* TODO: hexfloat *)
(* TODO: floats *)

let value =
  choice
    (concat number (fun x -> ret (LInt x)))
    (concat text (fun x -> ret (LString (KTextString, x))))

let tag = concat dot (fun _ -> uint)

let memberkey_cut =
  choice
    (concat hat (fun _ -> ret true))
    (ret false)

let bareword = id

let occur =
  choices
    [
      concat plus (fun _ -> ret (fun x -> GOneOrMore x));
      concat question (fun _ -> ret (fun x -> GZeroOrOne x));
(* TODO: bounds *)
      concat (* option(occur_from) *) star (* option(occur_to) *) (fun _ -> ret (fun x -> GZeroOrMore x));
    ]

let option_occur =
  choice
    occur
    (ret (fun (x: group) -> x))

let rec type_ () =
  concat (type1 ()) (fun x -> concat (type_tail ()) (fun xs -> ret (xs x)))

and type_tail () =
  choice
    (concat s (fun _ -> concat slash (fun _ -> concat (type1 ()) (fun xl -> concat (type_tail ()) (fun xr -> ret (fun (x: typ) -> TChoice (x, xr xl)))))))
    (ret (fun (x: typ) -> x))

and type1 () = type2 () (* option(type1_tail) *) 

(* TODO
type1_tail:
  | s rangeop_or_ctlop s type2

rangeop_or_ctlop: (* TODO *)
  | rangeop
  | ctlop
*)

and type2 () =
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
(* TODO: "#"DIGIT option(tag) *)
      concat pound (fun _ -> ret (TElem EAny));
    ]

and group () : (token, group) parser =
  concat (grpchoice ()) (fun a -> concat (group_tail ()) (fun q -> ret (q a)))

and group_tail () =
  choice
    (concat s (fun _ -> concat slashslash (fun _ -> concat s (fun _ -> concat (grpchoice ()) (fun a -> concat (group_tail ()) (fun q -> ret (fun (x: group) -> GChoice (x, q a))))))))
    (ret (fun (x: group) -> x))

and grpchoice () =
  choice
    (concat (grpent ()) (fun a -> concat (option (concat s (fun _ -> comma))) (fun _ -> concat (grpchoice ()) (fun q -> ret (GConcat (a, q))))))
    (ret GNop)

and grpent () =
  choices
    [
      concat option_occur (fun f -> concat (option_memberkey ()) (fun g -> concat (type_ ()) (fun x -> ret (f (g x)))));
      concat option_occur (fun f -> concat groupname (* option(genericarg) *) (fun g -> ret (f (GDef g))));
      concat option_occur (fun f -> concat lparen (fun _ -> concat s (fun _ -> concat (group ()) (fun g -> concat s (fun _ -> concat rparen (fun _ -> ret (f g)))))));
    ]

and option_memberkey () =
  choice
    (concat (memberkey ()) (fun x -> concat s (fun _ -> ret x)))
    (ret (fun x -> GElem (false, TElem EAny, x)))

and memberkey () =
  choices
    [
      concat (type1 ()) (fun key -> concat s (fun _ -> concat memberkey_cut (fun cut -> concat arrow (fun _ -> ret (fun x -> GElem (cut, key, x))))));
      concat bareword (fun key -> concat s (fun _ -> concat colon (fun _ -> ret (fun x -> GElem (true, TElem (ELiteral (LString (KTextString, key))), x)))));
      concat value (fun key -> concat s (fun _ -> concat colon (fun _ -> ret (fun x -> (GElem (true, TElem (ELiteral key), x))))));
    ]

let rec cddl () : (token, (string * CDDL_Spec_AST_Base.typ) list) parser =
  concat s (fun _ -> concat (nonempty_list (cddl_item ())) (fun l -> concat eof (fun _ -> ret l)))

and cddl_item () =
  concat (rule ()) (fun x -> concat s (fun _ -> ret x))

and rule () =
  concat typename (* option(genericparm) *) (fun name -> concat s (fun _ -> concat assignt (fun f -> concat s (fun _ -> concat (type_ ()) (fun t -> ret (f name t))))))
