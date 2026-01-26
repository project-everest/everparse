open ABNF
open Tokens
open Fstar_pluginlib
open FStar_Pervasives
open CDDL_Spec_AST_Base

type id_kind =
| Regular
| SocketType
| SocketGroup

type 'a thing_or_name = | Thing of 'a | Name of string

type program0 = (Prims.string * decl thing_or_name) Prims.list

type state = {
  sockets: (string * id_kind) list;
  result: program0;
}
type cddl_t = state
type 'a parser = (Tokens.token, state, 'a, cddl_t) ABNF.parser
type symbol = unit parser

let get_full_state () : (state * int) parser =
  fun buf k -> k (TokenBuffer.get_state buf, TokenBuffer.history_length buf)

let loop_detector : ((string * (state * int)), unit) Hashtbl.t =
  Hashtbl.create 16

let check_loop (x: (string * (state * int))) : bool =
  if Hashtbl.mem loop_detector x
  then true
  else begin
     Hashtbl.add loop_detector x ();
     false
    end

let debug
      (name: string)
      (f: 'a parser)
    : 'a parser
  = ABNF.debug
      name
      (concat (get_full_state ()) (fun state ->
           if check_loop (name, state)
           then fail
           else concat f (fun res ->
                    Hashtbl.remove loop_detector (name, state);
                    ret res
                  )
         )
      )

let terminal name f =
  terminal (fun x ->
      if enable_debug
      then begin
          print_spaces ();
          print_endline ("Entering terminal " ^ name ^ " with token " ^ show_token x);
        end;
      let res = f x in
      if enable_debug
      then begin
          print_spaces ();
          match res with
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
let amp = terminal "amp" (function AMP -> Some () | _ -> None)
let pound2 = terminal "pound2" (function POUND2 -> Some () | _ -> None)
let pound3 = terminal "pound3" (function POUND3 -> Some () | _ -> None)
let pound6 = terminal "pound6" (function POUND6 -> Some () | _ -> None)
let pound7 = terminal "pound7" (function POUND7 -> Some () | _ -> None)
let dotdotdot = terminal "dotdotdot" (function DOTDOTDOT -> Some () | _ -> None)
let dotdot = terminal "dotdot" (function DOTDOT -> Some () | _ -> None)
let dot = terminal "dot" (function DOT -> Some () | _ -> None)
let pound = terminal "pound"  (function POUND -> Some () | _ -> None)
let minus = terminal "minus" (function MINUS -> Some () | _ -> None)
let slashslash = terminal "slashslash" (function SLASHSLASH -> Some () | _ -> None)
let slashslasheq = terminal "slashslasheq" (function SLASHSLASHEQ -> Some () | _ -> None)
let slasheq = terminal "slasheq" (function SLASHEQ -> Some () | _ -> None)
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

let id = debug "id"
  (choices [
    concat raw_id (fun s -> ret (Regular, s));
    concat dollar (fun _ -> concat raw_id (fun s -> ret (SocketType, s)));
    concat dollardollar (fun _ -> concat raw_id (fun s -> ret (SocketGroup, s)));
  ])

let name =
  (concat id (fun ((k, n) as res) -> concat (get_state ()) (fun s ->
                                         begin match List.assoc_opt n s.sockets with
                                         | None ->
                                            let s' = { s with sockets = List.merge (fun (_, n1) (_, n2) -> compare n1 n2) [(n, k)] s.sockets } in
                                            concat (set_state s') (fun _ -> ret res)
                                         | Some k' ->
                                            if k = k'
                                            then ret res
                                            else fail
                                         end
  )))

let typename = debug "typename"
  (concat name (fun ((k, _) as res) -> match k with SocketGroup -> fail | _ -> ret res))

let groupname = debug "groupname"
  (concat name (fun ((k, _) as res) -> match k with SocketType -> fail | _ -> ret res))

let close_typ (t: typ thing_or_name) : typ =
  match t with
  | Thing t' -> t'
  | Name n -> TDef n

let close_group (t: group thing_or_name) : group =
  match t with
  | Thing t' -> t'
  | Name n -> GDef n

let assignt ((k, x): (id_kind * string)) = debug "assignt"
  (choice
    (concat eq (fun _ ->
      if k = Regular
      then ret (fun (t: typ thing_or_name) (l: (string * CDDL_Spec_AST_Base.decl thing_or_name) list) ->
               let t' = match t with
               | Thing t' -> Thing (CDDL_Spec_AST_Base.DType t')
               | Name n -> Name n
               in
               (x, t') :: l)
      else fail
    ))
    (concat slasheq (fun _ ->
      if k = SocketType
      then ret (fun (t: typ thing_or_name) (l: (string * CDDL_Spec_AST_Base.decl thing_or_name) list) ->
        let t = close_typ t in
        match List.assoc_opt x l with
        | None -> (x, Thing (CDDL_Spec_AST_Base.DType t)) :: l
        | Some t_ ->
           let t0 = match t_ with
             | Thing (CDDL_Spec_AST_Base.DType t0) -> t0
             | Name n -> TDef n
             | _ -> failwith "assignt: this should not happen. Please report"
           in
           (x, Thing (CDDL_Spec_AST_Base.DType (CDDL_Spec_AST_Elab_Base.mk_TChoice t0 t))) :: List.remove_assoc x l
      )
      else fail
    ))
  )

let assigng ((k, x) : (id_kind * string)) = debug "assigng"
  (choice
    (concat eq (fun _ ->
      if k = Regular
      then ret (fun (t: group thing_or_name) (l: (string * CDDL_Spec_AST_Base.decl thing_or_name) list) ->
               let t' = match t with
                 | Thing t' -> Thing (CDDL_Spec_AST_Base.DGroup t')
                 | Name n -> Name n
               in
               (x, t') :: l)
      else fail
    ))
    (concat slashslasheq (fun _ ->
      if k = SocketGroup
      then ret (fun (t: group thing_or_name) (l: (string * CDDL_Spec_AST_Base.decl thing_or_name) list) ->
        let t = close_group t in
        match List.assoc_opt x l with
        | None -> (x, Thing (CDDL_Spec_AST_Base.DGroup t)) :: l
        | Some t_ ->
           let t0 = match t_ with
             | Thing (CDDL_Spec_AST_Base.DGroup t0) -> t0
             | Name n -> GDef n
             | _ -> failwith "assigng: this should not happen. Please report"
           in
           (x, Thing (CDDL_Spec_AST_Base.DGroup (CDDL_Spec_AST_Driver.mk_GChoice t0 t))) :: List.remove_assoc x l
      )
      else fail
    ))
  )

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
    (concat text (fun x -> ret (LTextString (x))))
)

let tag = debug "tag" (concat dot (fun _ -> uint))

let memberkey_cut = debug "memberkey_cut" (
  choice
    (concat hat (fun _ -> ret true))
    (ret false)
)

let bareword = debug "bareword" id

let occur_bound = debug "occur_from" (
  choices
    [
      concat uint (fun x -> ret (Some x));
      ret None;
    ]
)

let occur = debug "occur" (
  choices
    [
      concat plus (fun _ -> ret (fun x -> Thing (GOneOrMore (close_group x))));
      concat question (fun _ -> ret (fun x -> Thing (GZeroOrOne (close_group x))));
      concat occur_bound (fun from -> concat star (fun _ -> concat occur_bound (fun to_ -> (* TODO: bounds *)
       if from = None && to_ = None then ret (fun x -> Thing (GZeroOrMore (close_group x))) else fail)));
    ]
)

let option_occur = debug "option_occur" (
  choice
    (concat occur (fun x -> concat s (fun _ -> ret x)))
    (ret (fun (x: group thing_or_name) -> x))
)

let optcom = debug "optcom" (concat s (fun _ -> option (concat comma (fun _ -> s))))

let rangeop =
  debug "rangeop"
    (choice
      (concat dotdotdot (fun _ -> ret (fun t1 t2 -> Thing (TRange (close_typ t1, false, close_typ t2)))))
      (concat dotdot (fun _ -> ret (fun t1 t2 -> Thing (TRange (close_typ t1, true, close_typ t2)))))
    )

let ctlop =
  debug "ctlop"
    (concat dot (fun _ -> concat id (fun s -> match s with
    | (Regular, "size") -> ret (fun t1 t2 -> Thing (TSize (close_typ t1, close_typ t2)))
    | (Regular, "everparse-det-cbor") -> ret (fun t1 t2 -> Thing (TDetCbor (close_typ t1, close_typ t2)))
    (* TODO: (non-injective) cbor *)
    | _ -> fail
    )))

let rangeop_or_ctlop =
  debug "rangeop_or_ctlop"
    (choice
      (concat rangeop (fun f -> ret f))
      (concat ctlop (fun f -> ret f))
    )

let close_group_thing_option x = match x with
| None -> Thing GNop
| Some x -> x

let rec type_ () = debug "type" (
  concat (type1 ()) (fun x -> concat (type_tail ()) (fun xs -> ret (xs x)))
)

and type_tail () = debug "type_tail" (
  choice
    (concat s (fun _ -> concat slash (fun _ -> concat s (fun _ -> concat (type1 ()) (fun xl -> concat (type_tail ()) (fun (xr: typ thing_or_name -> typ thing_or_name) -> ret (fun (x: typ thing_or_name) -> Thing (CDDL_Spec_AST_Elab_Base.mk_TChoice (close_typ x) (close_typ (xr xl))))))))))
    (ret (fun (x: typ thing_or_name) -> x))
)

and type1 () = debug "type1" (concat (type2 ()) (fun (t, needs_space) -> concat (type1_tail needs_space) (fun f -> ret (f t))))

(* `needs_space` implements the remark "space may be needed before the operator if type2 ends in a name" *)
and type1_tail (needs_space: bool) =
  debug "type1_tail"
    (choice
      (concat (if needs_space then nonempty_s else s) (fun _ -> concat rangeop_or_ctlop (fun f -> concat s (fun _ -> concat (type2 ()) (fun (t2, _) -> ret (fun t1 -> f t1 t2))))))
      (ret (fun t -> t))
    )

and type2 () = debug "type2" (
  choices
    [
      concat value (fun x -> ret (Thing (TElem (ELiteral x)), false));
      concat typename (fun (k, x) -> (* option(genericarg) *) ret (
                                         begin match k with
                                         | Regular -> Name x
                                         | SocketType -> Thing (TDef x)
                                         | _ -> failwith "type2: typename"
                                         end, true));
      concat lparen (fun _ -> concat s (fun _ -> concat (type_ ()) (fun x -> concat s (fun _ -> concat rparen (fun _ -> ret (x, false))))));
      concat lbrace (fun _ -> concat s (fun _ -> concat (group ()) (fun x -> concat s (fun _ -> concat rbrace (fun _ -> ret (Thing (TMap (close_group x)), false))))));
      concat lbrack (fun _ -> concat s (fun _ -> concat (group ()) (fun x -> concat s (fun _ -> concat rbrack (fun _ -> ret (Thing (TArray (close_group x)), false))))));
(* TODO: "~" s typename option(genericarg) *)
(* TODO: "&" s "(" s group s ")" *)
      concat amp (fun _ -> concat s (fun _ -> concat lparen (fun _ -> concat s (fun _ -> concat bareword (fun (_, name) -> concat s (fun _ -> concat colon (fun _ -> concat s (fun _ -> concat (type_ ()) (fun ty -> concat s (fun _ -> concat rparen (fun _ -> ret (Thing (TNamed (name, close_typ ty)), false))))))))))));
(* TODO: "&" s groupname option(genericarg) *)
      concat pound6 (fun _ -> concat (option tag) (fun tag -> concat lparen (fun _ -> concat s (fun _ -> concat (type_ ()) (fun x -> concat s (fun _ -> concat rparen (fun _ -> ret (Thing (TTagged (tag, close_typ x)), false))))))));
(* TODO: generalize "#"DIGIT option(tag) *)
      concat pound0 (fun _ -> ret (Thing (TElem EUInt), false));
      concat pound1 (fun _ -> ret (Thing (TElem ENInt), false));
      concat pound2 (fun _ -> ret (Thing (TElem EByteString), false));
      concat pound3 (fun _ -> ret (Thing (TElem ETextString), false));
      concat pound7 (fun _ -> concat (option tag) (fun tag -> ret (Thing (match tag with None -> TElem ESimple | Some v -> TElem (ELiteral (LSimple v))), false)));
      concat pound (fun _ -> ret (Thing (TElem EAny), false));
    ]
)

and group () : group thing_or_name parser = debug "group" (
  concat (grpchoice ()) (fun a -> concat (group_tail ()) (fun q -> ret (q a)))
)

and group_tail () : (group thing_or_name option -> group thing_or_name) parser = debug "group_tail" (
  choice
    (concat s (fun _ -> concat slashslash (fun _ -> concat s (fun _ -> concat (grpchoice ()) (fun a -> concat (group_tail ()) (fun q -> ret (fun (x: group thing_or_name option) -> Thing (CDDL_Spec_AST_Driver.mk_GChoice (close_group (close_group_thing_option x)) (close_group (q a))))))))))
    (ret (fun (x: group thing_or_name option) -> close_group_thing_option x))
)

and grpchoice () = debug "grpchoice" (
  choice
    (concat (grpent ()) (fun a -> concat optcom (fun com -> concat (grpchoice ()) (fun q ->
                                                              match q with
                                                              | None -> ret (Some (
                                                                                 match com with
                                                                                 | None -> a
                                                                                 | Some _ -> Thing (close_group a)
                                                                          ))
                                                              | Some q -> ret (Some (Thing (CDDL_Spec_AST_Driver.mk_GConcat (close_group a) (close_group q))))
    ))))
    (ret None)
)

and grpent () = debug "grpent" (
  choices
    [
      concat option_occur (fun f -> concat (option_memberkey ()) (fun g -> concat (type_ ()) (fun x -> ret (f (g x)))));
      concat option_occur (fun f -> concat groupname (* option(genericarg) *) (fun (k, g) -> ret (f (match k with
                                                                                                     | Regular -> Name g
                                                                                                     | SocketGroup -> Thing (GDef g)
                                                                                                     | _ -> failwith "grpent: groupname"
        ))));
      concat option_occur (fun f -> concat lparen (fun _ -> concat s (fun _ -> concat (group ()) (fun g -> concat s (fun _ -> concat rparen (fun _ -> ret (f g)))))));
    ]
)

and option_memberkey () = debug "option_memberkey" (
  choice
    (concat (memberkey ()) (fun x -> concat s (fun _ -> ret x)))
    (ret (fun x -> match x with
                   | Name s -> Name s
                   | Thing t -> Thing (GElem (false, TElem EAny, close_typ x))
    ))
)

and memberkey () = debug "memberkey" (
  choices
    [
      concat (type1 ()) (fun key -> concat s (fun _ -> concat memberkey_cut (fun cut -> concat arrow (fun _ -> ret (fun x -> Thing (GElem (cut, close_typ key, close_typ x)))))));
      concat bareword (fun (k, key) -> if k <> Regular then fail else concat s (fun _ -> concat colon (fun _ -> ret (fun x -> Thing (GElem (true, TElem (ELiteral (LTextString (key))), close_typ x))))));
      concat value (fun key -> concat s (fun _ -> concat colon (fun _ -> ret (fun x -> Thing (GElem (true, TElem (ELiteral key), close_typ x))))));
    ]
)

let rec cddl () : cddl_t parser = debug_start "cddl" (
                                      (* rev needed because assignment operators cons definitions in the reverse order of their parsing *)
  concat s (fun _ -> concat (nonempty_unit_fold_left (cddl_item ())) (fun l -> concat eof (fun _ -> get_state ())))
)

and cddl_item () : unit parser = debug "cddl_item" (
  concat (rule ()) (fun _ -> s)
)

and rule () : unit parser =
  debug "rule"
    (choice
       (concat typename (* option(genericparm) *) (fun name -> concat s (fun _ -> concat (assignt name) (fun f -> concat s (fun _ -> concat (type_ ()) (fun t -> concat (get_state ()) (fun env -> let env' = { env with result = f t env.result } in set_state env')))))))
       (concat groupname (* option(genericparm) *) (fun name -> concat s (fun _ -> concat (assigng name) (fun f -> concat s (fun _ -> concat (grpent ()) (fun t -> concat (get_state ()) (fun env -> let env' = { env with result = f t env.result } in set_state env')))))))
    )
