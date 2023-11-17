module Z3TestGen
module Printf = FStar.Printf
open FStar.All
open FStar.Mul

module A = Ast
module T = Target
module I = InterpreterTarget

let prelude : string =
"
(set-option :produce-models true)
(declare-datatypes () ((State (mk-state (input-size Int) (choice-index Int)))))
(declare-datatypes () ((Result (mk-result (return-value Int) (after-state State)))))

(define-fun parse-empty ((x State)) Result
  (mk-result 0 x)
)

(declare-fun choose (Int) Int)
(assert (forall ((i Int))
  (and (<= 0 (choose i)) (< (choose i) 256))
))

(define-fun parse-false ((x State)) State
  (mk-state -1 (choice-index x))
)

(define-fun parse-all-bytes ((x State)) State
  (if (<= (input-size x) 0)
    x
    (mk-state 0 (+ (choice-index x) (input-size x)))
  )
)

(define-fun parse-all-zeros ((x State)) State
  (if (<= (input-size x) 0)
    x
    (mk-state
      (if
        (forall ((j Int))
          (if (and (<= 0 j) (< j (input-size x)))
            (= (choose (+ (choice-index x) j)) 0)
            true
          )
        )
        0
        -1
      )
      (+ (choice-index x) (input-size x))
    )
  )
)

(define-fun parse-u8 ((x State)) Result
  (mk-result
    (choose (choice-index x))
    (mk-state (- (input-size x) 1) (+ (choice-index x) 1))
  )
)

(define-fun parse-u16-be ((x State)) Result
  (mk-result
    (+ (choose (+ 1 (choice-index x)))
      (* 256
        (choose (+ 0 (choice-index x)))
      )
    )
    (mk-state (- (input-size x) 2) (+ (choice-index x) 2))
  )
)

(define-fun parse-u16-le ((x State)) Result
  (mk-result
    (+ (choose (+ 0 (choice-index x)))
      (* 256
        (choose (+ 1 (choice-index x)))
      )
    )
    (mk-state (- (input-size x) 2) (+ (choice-index x) 2))
  )
)

(define-fun parse-u32-be ((x State)) Result
  (mk-result
    (+ (choose (+ 3 (choice-index x)))
      (* 256
        (+ (choose (+ 2 (choice-index x)))
          (* 256
            (+ (choose (+ 1 (choice-index x)))
              (* 256
                (choose (+ 0 (choice-index x)))
              )
            )
          )
        )
      )
    )
    (mk-state (- (input-size x) 4) (+ (choice-index x) 4))
  )
)

(define-fun parse-u32-le ((x State)) Result
  (mk-result
    (+ (choose (+ 0 (choice-index x)))
      (* 256
        (+ (choose (+ 1 (choice-index x)))
          (* 256
            (+ (choose (+ 2 (choice-index x)))
              (* 256
                (choose (+ 3 (choice-index x)))
              )
            )
          )
        )
      )
    )
    (mk-state (- (input-size x) 4) (+ (choice-index x) 4))
  )
)

(define-fun parse-u64-be ((x State)) Result
  (mk-result
    (+ (choose (+ 7 (choice-index x)))
      (* 256
        (+ (choose (+ 6 (choice-index x)))
          (* 256
            (+ (choose (+ 5 (choice-index x)))
              (* 256
                (+ (choose (+ 4 (choice-index x)))
                  (* 256
                    (+ (choose (+ 3 (choice-index x)))
                      (* 256
                        (+ (choose (+ 2 (choice-index x)))
                          (* 256
                            (+ (choose (+ 1 (choice-index x)))
                              (* 256
                                (choose (+ 0 (choice-index x)))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (mk-state (- (input-size x) 8) (+ (choice-index x) 8))
  )
)

(define-fun parse-u64-le ((x State)) Result
  (mk-result
    (+ (choose (+ 0 (choice-index x)))
      (* 256
        (+ (choose (+ 1 (choice-index x)))
          (* 256
            (+ (choose (+ 2 (choice-index x)))
              (* 256
                (+ (choose (+ 3 (choice-index x)))
                  (* 256
                    (+ (choose (+ 4 (choice-index x)))
                      (* 256
                        (+ (choose (+ 5 (choice-index x)))
                          (* 256
                            (+ (choose (+ 6 (choice-index x)))
                              (* 256
                                (choose (+ 7 (choice-index x)))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (mk-state (- (input-size x) 8) (+ (choice-index x) 8))
  )
)

(define-fun-rec pow-2 ((amount Int)) Int
  (if (<= amount 0)
    1
    (* 2 (pow-2 (- amount 1)))
  )
)

;; see LowParse.BitFields.get_bitfield_eq
(define-fun get-bitfield-lsb ((nbBits Int) (value Int) (bitsFrom Int) (bitsTo Int)) Int
  (mod (div value (pow-2 bitsFrom)) (pow-2 (- bitsTo bitsFrom)))
)

;; see EverParse3d.Prelude.StaticHeader
(define-fun get-bitfield-msb ((nbBits Int) (value Int) (bitsFrom Int) (bitsTo Int)) Int
  (get-bitfield-lsb nbBits value (- nbBits bitsTo) (- nbBits bitsFrom))
)

(declare-const initial-input-size Int)
(assert (>= initial-input-size 0))
(define-fun initial-state () State (mk-state initial-input-size 0))

"

let mk_constant = function
  | A.Unit -> "0"
  | A.Int _ x -> string_of_int x
  | A.XInt _ x -> string_of_int (OS.int_of_string x)
  | A.Bool true -> "true"
  | A.Bool false -> "false"

let mk_app fn = function
  | None -> fn
  | Some args -> Printf.sprintf "(%s %s)" fn args

let assert_some = function
  | None -> failwith "assert_some"
  | Some x -> x

let is_bitwise_op (x: T.op) : Tot (option A.integer_type) =
  match x with
  | T.BitwiseAnd a
  | T.BitwiseXor a
  | T.BitwiseOr a
  | T.BitwiseNot a
  | T.ShiftLeft a
  | T.ShiftRight a
  -> Some a
  | _ -> None

let mk_bitwise_op (op: string) (bitvec_args: option string) : ML string =
  mk_app "bv2int" (Some (mk_app op bitvec_args))

let integer_type_bit_size = function
| A.UInt8 -> 8
| A.UInt16 -> 16
| A.UInt32 -> 32
| A.UInt64 -> 64

let mk_bitwise_not (a: A.integer_type) (bitvec_arg: option string) : ML string =
  match bitvec_arg with
  | None -> failwith "ill-formed bitwise_not"
  | Some arg -> "(bv2int (bvxor "^arg^" #b"^String.make (integer_type_bit_size a) '1'^"))"

let mk_op : T.op -> option string -> ML string = function
  | T.Eq -> mk_app "="
  | T.Neq -> (fun s -> mk_app "not" (Some (mk_app "=" s)))
  | T.And -> mk_app "and"
  | T.Or -> mk_app "or"
  | T.Not -> mk_app "not"
  | T.Plus _ -> mk_app "+"
  | T.Minus _ -> mk_app "-"
  | T.Mul _ -> mk_app "*"
  | T.Division _ -> mk_app "div"
  | T.Remainder _ -> mk_app "mod"
  | T.BitwiseAnd _ -> mk_bitwise_op "bvand"
  | T.BitwiseXor _ -> mk_bitwise_op "bvxor"
  | T.BitwiseOr _ -> mk_bitwise_op "bvor"
  | T.BitwiseNot a -> mk_bitwise_not a
  | T.ShiftLeft _ -> mk_bitwise_op "bvshl"
  | T.ShiftRight _ -> mk_bitwise_op "bvlshr"
  | T.LT _ -> mk_app "<"
  | T.GT _ -> mk_app ">"
  | T.LE _ -> mk_app "<="
  | T.GE _ -> mk_app ">="
  | T.IfThenElse -> mk_app "if"
  | T.BitFieldOf size order -> (fun arg -> Printf.sprintf "(get-bitfield-%ssb %d %s)" (match order with A.LSBFirst -> "l" | A.MSBFirst -> "m") size (assert_some arg))
  | T.Cast _ _ -> assert_some (* casts allowed only if they are proven not to lose precision *)
  | T.Ext s -> mk_app s

let ident_to_string = A.ident_to_string

let mk_bitwise_arg (t: A.integer_type) (arg: string) : Tot string =
  mk_app ("(_ int2bv "^string_of_int (integer_type_bit_size t)^")") (Some arg)

let mk_maybe_bitwise_arg (t: option A.integer_type) (arg: string) : Tot string =
  match t with
  | None -> arg
  | Some t -> mk_bitwise_arg t arg

let rec mk_expr (e: T.expr) : ML string = match fst e with
  | T.Constant c -> mk_constant c
  | T.Identifier i -> ident_to_string i
  | T.App hd args -> mk_op hd (mk_args (is_bitwise_op hd) args)
  | _ -> failwith "mk_expr: not supported"

and mk_args_aux (is_bitwise_op: option A.integer_type) accu : (list T.expr -> ML string) = function
  | [] -> accu
  | a :: q -> mk_args_aux is_bitwise_op (Printf.sprintf "%s %s" accu (mk_maybe_bitwise_arg is_bitwise_op (mk_expr a))) q

and mk_args (is_bitwise_op: option A.integer_type) (l: list T.expr) : ML (option string) = match l with
  | [] -> None
  | a :: q -> Some (mk_args_aux is_bitwise_op (mk_maybe_bitwise_arg is_bitwise_op (mk_expr a)) q)

type reading = { call: string }
type not_reading = { call: string }

type binders = {
  is_empty: bool;
  bind: string;
  args: string;
}

let empty_binders : binders = {
  is_empty = true;
  bind = "";
  args = "";
}

let push_binder (name: string) (typ: string) (b: binders) : binders = {
  is_empty = false;
  bind = Printf.sprintf "(%s %s) %s" name typ b.bind;
  args = Printf.sprintf " %s%s" name b.args;
}

let mk_function_call (name: string) (b: binders) =
  Printf.sprintf "%s%s" name b.args

type parser (a: Type) =
  (* name *) string ->
  (* binders *) binders ->
  (* is_toplevel *) bool ->
  (* out *) (string -> ML unit) ->
  ML a

let unsupported_parser (s: string) (a: Type) : Tot (parser a) =
  fun _ _ _ _ -> failwith (Printf.sprintf "unsupported parser: %s" s)

let leaf_reading_parser (name: string) : parser reading =
  fun _ _ _ _ -> { call = name }

let readable_itype_parser_suffix (i: I.itype) : Tot string = match i with
  | I.UInt8 | I.UInt8BE -> "u8"
  | I.UInt16 -> "u16-le"
  | I.UInt16BE -> "u16-be"
  | I.UInt32 -> "u32-le"
  | I.UInt32BE -> "u32-be"
  | I.UInt64 -> "u64-le"
  | I.UInt64BE -> "u64-be"
  | I.Unit -> "empty"
  | I.AllBytes -> "all-bytes"
  | I.AllZeros -> "all-zeros"

let parse_readable_itype (i: I.readable_itype) : Tot (parser reading) =
  leaf_reading_parser ("parse-" ^ readable_itype_parser_suffix i)

let mk_wrap_parser
  (name: string)
  (binders: string)
  (body: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (after-state ("^body^" "^input^"))
 )
"

let wrap_parser (p: parser reading) : parser not_reading =
  fun name binders _ out ->
    let name' = Printf.sprintf "%s-wrapped" name in
    let body = p name' binders false out in
    out (mk_wrap_parser name binders.bind body.call);
    { call = mk_function_call name binders }

let mk_toplevel_parser
  (name: string)
  (binders: string)
  (body: string)
: string
= let input = Printf.sprintf "%s-input" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   ("^body^" "^input^")
 )
"

let maybe_toplevel_parser (p: parser not_reading) : parser not_reading =
  fun name binders is_toplevel out ->
    if is_toplevel
    then begin
      let name' = Printf.sprintf "%s-body" name in
      let body = p name' binders false out in
      out (mk_toplevel_parser name binders.bind body.call);
      { call = mk_function_call name binders }
    end
    else p name binders false out

let parse_all_bytes : parser not_reading =
  maybe_toplevel_parser (fun _ _ _ _ -> { call = "parse-all-bytes" })

let parse_all_zeros : parser not_reading =
  maybe_toplevel_parser (fun _ _ _ _ -> { call = "parse-all-zeros" })

let parse_itype  : I.itype -> parser not_reading = function
  | I.AllBytes -> parse_all_bytes
  | I.AllZeros -> parse_all_zeros
  | i -> wrap_parser (parse_readable_itype i)

let mk_app_without_paren id args =
  mk_args_aux None (ident_to_string id) args
  
let parse_readable_app
  (hd: A.ident)
  (args: list I.expr)
: Tot (parser reading)
= fun _ _ _ _ -> { call = mk_app_without_paren hd args }

let parse_readable_dtyp
  (d: I.readable_dtyp)
: Tot (parser reading)
= match d with
  | I.DT_IType i -> parse_readable_itype i
  | I.DT_App _ hd args -> parse_readable_app hd args

let parse_not_readable_app
  (hd: A.ident)
  (args: list I.expr)
: Tot (parser not_reading)
= maybe_toplevel_parser (fun _ _ _ _ -> { call = mk_app_without_paren hd args })

let parse_dtyp
  (d: I.dtyp)
: Tot (parser not_reading)
= if I.allow_reader_of_dtyp d
  then wrap_parser (parse_readable_dtyp d)
  else match d with
    | I.DT_IType i -> parse_itype i
    | I.DT_App _ hd args -> parse_not_readable_app hd args

let parse_false : parser not_reading =
  maybe_toplevel_parser (fun _ _ _ _ -> { call = "parse-false" })

let parse_denoted (d: I.dtyp) : parser not_reading =
  parse_dtyp d

let mk_parse_pair
  (name: string)
  (binders: string)
  (fst: string)
  (snd: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (let (("^tmp^" ("^fst^" "^input^")))
     (if (< (input-size "^tmp^") 0)
       "^tmp^"
       ("^snd^" "^tmp^")
     )
   )
 )
"

let parse_pair (fst: parser not_reading) (snd: parser not_reading) : parser not_reading =
  fun name binders _ out ->
    let name_fst = Printf.sprintf "%s-fst" name in
    let body_fst = fst name_fst binders false out in
    let name_snd = Printf.sprintf "%s-snd" name in
    let body_snd = snd name_snd binders false out in
    out (mk_parse_pair name binders.bind body_fst.call body_snd.call);
    { call = mk_function_call name binders }

let parse_square (p: parser not_reading) : parser not_reading =
  fun name binders _ out ->
    let body_name = Printf.sprintf "%s-snd" name in
    let body = p body_name binders false out in
    out (mk_parse_pair name binders.bind body.call body.call);
    { call = mk_function_call name binders }

let mk_parse_dep_pair_with_refinement
  (name: string)
  (binders: string)
  (dfst: string)
  (cond_binder_name: string)
  (cond: string)
  (dsnd_binder_name: string)
  (dsnd: string) (* already contains the new argument *)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (let (("^tmp^" ("^dfst^" "^input^")))
     (if (< (input-size (after-state "^tmp^")) 0)
       (after-state "^tmp^")
       (if (let (("^cond_binder_name^" (return-value "^tmp^"))) "^cond^")
         (let (("^dsnd_binder_name^" (return-value "^tmp^")))
           ("^dsnd^" (after-state "^tmp^"))
         )
         (mk-state -1 (choice-index (after-state "^tmp^")))
       )
     )
   )
 )
"

let parse_dep_pair_with_refinement_gen (tag: parser reading) (cond_binder: string) (cond: unit -> ML string) (payload_binder: string) (payload: parser not_reading) : parser not_reading =
  fun name binders _ out ->
    let name_tag = Printf.sprintf "%s-tag" name in
    let body_tag = tag name_tag binders false out in
    let binders' = push_binder payload_binder "Int" binders in (* TODO: support more types *)
    let name_payload = Printf.sprintf "%s-payload" name in
    let body_payload = payload name_payload binders' false out in
    out (mk_parse_dep_pair_with_refinement name binders.bind body_tag.call cond_binder (cond ()) payload_binder body_payload.call);
    { call = mk_function_call name binders }

let parse_dep_pair_with_refinement (tag: parser reading) (cond_binder: A.ident) (cond: unit -> ML string) (payload_binder: A.ident) (payload: parser not_reading) : parser not_reading =
  parse_dep_pair_with_refinement_gen tag (ident_to_string cond_binder) cond (ident_to_string payload_binder) payload

let parse_dep_pair (tag: parser reading) (new_binder: A.ident) (payload: parser not_reading) : parser not_reading =
  parse_dep_pair_with_refinement tag new_binder (fun _ -> "true") new_binder payload

let parse_refine (tag: parser reading) (cond_binder: A.ident) (cond: unit -> ML string) : parser not_reading =
  parse_dep_pair_with_refinement tag cond_binder cond cond_binder (parse_itype I.Unit)

let mk_parse_ifthenelse
  (name: string)
  (binders: string)
  (cond: string)
  (f_then: string)
  (f_else: string)
: string
= let input = Printf.sprintf "%s-input" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (if "^cond^"
     ("^f_then^" "^input^")
     ("^f_else^" "^input^")
   )
 )
"

let parse_ifthenelse (cond: unit -> ML string) (pthen: parser not_reading) (pelse: parser not_reading) : parser not_reading =
  fun name binders _ out ->
    let name_then = Printf.sprintf "%s-then" name in
    let body_then = pthen name_then binders false out in
    let name_else = Printf.sprintf "%s-else" name in
    let body_else = pelse name_else binders false out in
    out (mk_parse_ifthenelse name binders.bind (cond ()) body_then.call body_else.call);
    { call = mk_function_call name binders }

let mk_parse_exact
  (name: string)
  (binders: string)
  (body: string)
  (size: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let sz = Printf.sprintf "%s-size" name in
  let res = Printf.sprintf "%s-res" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
  (let (("^sz^" "^size^"))
    (if (< (input-size "^input^") "^sz^")
      (mk-state -1 (choice-index "^input^"))
      (let (("^res^" ("^body^" (mk-state "^sz^" (choice-index "^input^")))))
        (mk-state
          (if (= (input-size "^res^") 0)
            (- (input-size "^input^") "^sz^")
            -1
          )
          (choice-index "^res^")
        )
      )
    )
  )
)
"

let parse_exact
  (size: unit -> ML string)
  (body: parser not_reading)
: Tot (parser not_reading)
= fun name binders _ out ->
    let body_name = Printf.sprintf "%s-body" name in
    let body = body body_name binders false out in
    out (mk_parse_exact name binders.bind body.call (size ()));
    { call = mk_function_call name binders }

let parse_at_most
  (size: unit -> ML string)
  (body: parser not_reading)
: Tot (parser not_reading)
= parse_exact size (parse_pair body parse_all_bytes)

(*
let mk_parse_list_one
  (name: string)
  (binders: string)
  (p: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let res = Printf.sprintf "%s-res" name in
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
  (if (= (seq.len "^input^") 0)
    (seq.unit 0)
    (let (("^res^" ("^p^" "^input^")))
      (if (= (seq.len "^res^") 0)
        (as seq.empty (Seq Int))
        (if (= (seq.nth "^res^" 0) 0)
          (as seq.empty (Seq Int))
          "^res^"
        )
      )
    )
  )
)
"

let parse_list_one
  (body: parser not_reading)
: Tot (parser not_reading)
= fun name binders _ out ->
    let body_name = Printf.sprintf "%s-body" name in
    let body = body body_name binders false out in
    out (mk_parse_list_one name binders.bind body.call);
    { call = mk_function_call name binders }

let rec parse_list_bounded'
  (body: parser not_reading)
  (logn: nat)
: Tot (parser not_reading)
  (decreases logn)
= if logn = 0
  then parse_list_one body
  else
    let logn' = logn - 1 in
    parse_square (parse_list_bounded' body logn')

let parse_list_bounded body = parse_list_bounded' body 3 // 64
*)

let mk_parse_list
  (name: string)
  (rec_call: string)
  (binders: string)
  (body: string)
: string
= let input = Printf.sprintf "%s-input" name in
"(define-fun-rec "^name^" ("^binders^"("^input^" State)) State
  (if (<= (input-size "^input^") 0)
    "^input^"
    ("^rec_call^" ("^body^" "^input^"))
  )
)
"

let parse_list
  (body: parser not_reading)
: Tot (parser not_reading)
= fun name binders _ out ->
    let rec_call = mk_function_call name binders in
    let body_name = Printf.sprintf "%s-body" name in
    let body = body body_name binders false out in
    out (mk_parse_list name rec_call binders.bind body.call);
    { call = rec_call }

let parse_nlist
  (size: unit -> ML string)
  (body: parser not_reading)
: Tot (parser not_reading)
= parse_exact size (parse_list body)

let mk_parse_string
  (name: string)
  (rec_call: string)
  (binders: string)
  (body: string)
  (terminator: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun-rec "^name^" ("^binders^"("^input^" State)) State
  (let (("^tmp^" ("^body^" "^input^")))
    (if (< (choice-index (after-state "^tmp^")) 0)
      (mk-state -1 (choice-index (after-state "^tmp^")))
      (if (= (return-value "^tmp^") "^terminator^")
        (after-state "^tmp^")
        ("^rec_call^" (after-state "^tmp^"))
      )
    )
  )
)
"

let parse_string
  (body: parser reading)
  (terminator: (unit -> ML string))
: Tot (parser not_reading)
= fun name binders _ out ->
    let rec_call = mk_function_call name binders in
    let body_name = Printf.sprintf "%s-body" name in
    let body = body body_name binders false out in
    out (mk_parse_string name rec_call binders.bind body.call (terminator ()));
    { call = rec_call }

let rec type_has_actions = function
  | I.T_with_dep_action _ _ _
  | I.T_dep_pair_with_action _ _ _ _
  | I.T_refine_with_action _ _ _ _
  | I.T_dep_pair_with_refinement_and_action _ _ _ _ _
  | I.T_with_action _ _ _
    -> true
  | I.T_false _
  | I.T_denoted _ _
  | I.T_refine _ _ _
  | I.T_string _ _ _
    -> false
  | I.T_if_else _ t1 t2
  | I.T_pair _ t1 t2 ->
    type_has_actions t1 || type_has_actions t2
  | I.T_at_most _ _ t
  | I.T_exact _ _ t
  | I.T_nlist _ _ t
  | I.T_with_comment _ t _
  | I.T_dep_pair_with_refinement _ _ _ (_, t)
  | I.T_dep_pair _ _ (_, t) ->
    type_has_actions t

let rec parse_typ (t : I.typ) : Pure (parser not_reading)
  (requires (type_has_actions t == false))
  (ensures (fun _ -> True))
= match t with
  | I.T_false _ -> parse_false
  | I.T_denoted _ d -> parse_denoted d
  | I.T_pair _ t1 t2 -> parse_pair (parse_typ t1) (parse_typ t2)
  | I.T_dep_pair _ t1 (lam, t2) -> parse_dep_pair (parse_readable_dtyp t1) lam (parse_typ t2)
  | I.T_refine _ base (lam, cond) -> parse_refine (parse_readable_dtyp base) lam (fun _ -> mk_expr cond)
  | I.T_dep_pair_with_refinement _ base (lam_cond, cond) (lam_k, k) -> parse_dep_pair_with_refinement (parse_readable_dtyp base) lam_cond (fun _ -> mk_expr cond) lam_k (parse_typ k)
  | I.T_if_else cond t1 t2 -> parse_ifthenelse (fun _ -> mk_expr cond) (parse_typ t1) (parse_typ t2)
  | I.T_with_comment _ base _ -> parse_typ base
  | I.T_at_most _ size body -> parse_at_most (fun _ -> mk_expr size) (parse_typ body)
  | I.T_exact _ size body -> parse_exact (fun _ -> mk_expr size) (parse_typ body)
  | I.T_string _ elt terminator -> parse_string (parse_readable_dtyp elt) (fun _ -> mk_expr terminator)
  | I.T_nlist _ size body -> parse_nlist (fun _ -> mk_expr size) (parse_typ body)

type arg_type =
| ArgInt of A.integer_type
| ArgBool
| ArgPointer

let arg_type_of_typ (t: T.typ) : Tot (option arg_type) =
  match t with
  | T.T_pointer _
  | T.T_app _ A.KindOutput _
  | T.T_app _ A.KindExtern _
  | T.T_app {v = {modul_name = None; name = "PUINT8"}} _ _
    -> Some ArgPointer
  | T.T_app {v = {modul_name = None; name = "Bool"}} _ _
    -> Some ArgBool
  | T.T_app i _ _
    ->
    begin match A.maybe_as_integer_typ i with
    | Some t -> Some (ArgInt t)
    | None -> None
    end
  | _ -> None

let smt_type_of_typ (t: T.typ) : Tot string =
  match arg_type_of_typ t with
  | Some ArgBool -> "Bool"
  | _ -> "Int"

let rec binders_of_params = function
| [] -> empty_binders
| (id, t) :: q -> push_binder (ident_to_string id) (smt_type_of_typ t) (binders_of_params q)

let mk_definition
  (name: string)
  (binders: string)
  (typ: string)
  (body: string)
: Tot string
= "(define-fun "^name^" ("^binders^") "^typ^" "^body^")"

let produce_definition
  (i: A.ident)
  (param: list T.param)
  (typ: T.typ)
  (body: T.expr)
  (out: string -> ML unit)
: ML unit
= let binders = binders_of_params param in
  out (mk_definition (ident_to_string i) binders.bind (smt_type_of_typ typ) (mk_expr body))

let produce_not_type_decl (a: I.not_type_decl) (out: string -> ML unit) : ML unit =
  match fst a with
  | T.Definition (i, param, typ, body) ->
    produce_definition i param typ body out
  | T.Assumption _ -> failwith "produce_not_type_decl: unsupported"
  | T.Output_type _
  | T.Output_type_expr _ _
  | T.Extern_type _
  | T.Extern_fn _ _ _
  -> ()

let prog = list (string & list arg_type)

let produce_type_decl (out: string -> ML unit) (accu: prog) (a: I.type_decl) : ML prog =
  let binders = binders_of_params a.name.td_params in
  let name = ident_to_string a.name.td_name in
  if type_has_actions a.typ then failwith (Printf.sprintf "produce_type_decl: %s still has some actions" name);
  let _ = parse_typ a.typ name binders true out in
  (name, List.map (fun (i, ty) -> match arg_type_of_typ ty with Some t -> t | None -> failwith (Printf.sprintf "Parser %s has unsupported argument type for %s" name (ident_to_string i))) a.name.td_params) :: accu

let produce_decl (out: string -> ML unit) (accu: prog) (a: I.decl) : ML prog =
  match a with
  | Inl a -> produce_not_type_decl a out; accu
  | Inr a -> produce_type_decl out accu a

let produce_decls (out: string -> ML unit) (accu: prog) (l: list I.decl) : ML prog =
  List.fold_left (produce_decl out) accu l

(* Produce the SMT2 encoding of the parser spec *)

let with_out_file
  (#a: Type)
  (name: string)
  (body: ((string -> ML unit) -> ML a))
: ML a
= let fd = FStar.IO.open_write_file name in
  let res = body (FStar.IO.write_string fd) in
  FStar.IO.close_write_file fd;
  res

let with_option_out_file
  (#a: Type)
  (name: option string)
: Tot ((body: ((string -> ML unit) -> ML a)) -> ML a)
= match name with
  | Some name -> with_out_file name
  | None -> (fun body -> body (fun _ -> ()))

(* Ask Z3 for test witnesses *)

let read_witness (z3: Z3.z3) : ML (Seq.seq int) =
  z3.to_z3 "(get-value (state-witness-size))\n";
  let (_, witness_size) = Lisp.read_int_from z3.from_z3 "state-witness-size" in
  let rec aux (accu: Seq.seq int) (remaining: int) : ML (Seq.seq int) =
    if remaining <= 0
    then accu
    else
      let index = remaining - 1 in
      let _ = z3.to_z3 (Printf.sprintf "(eval (choose %d))\n" index) in
      let v = Lisp.read_bare_int_from z3.from_z3 in
      aux (Seq.cons v accu) index
  in
  aux Seq.empty witness_size

let rec read_witness_args (z3: Z3.z3) (accu: list string) (n: nat) : ML (list string) =
  if n = 0
  then accu
  else begin
    let n' = n - 1 in
    z3.to_z3 (Printf.sprintf "(get-value (arg-%d))\n" n');
    let arg = Lisp.read_any_from z3.from_z3 (Printf.sprintf "arg-%d" n') in
    read_witness_args z3 (arg :: accu) n'
  end

let module_and_validator_name
  (s: string)
: ML (string & string)
= match String.split ['.'] s with
  | [modul; fn] -> modul, Target.validator_name modul fn
  | _ -> failwith "Z3TestGen.validator_name"

let rec print_witness_args_as_c
  (out: (string -> ML unit))
  (l: list arg_type) (args: list string)
: ML unit
= match l, args with
  | ArgPointer :: q, _ ->
    out "NULL, ";
    print_witness_args_as_c out q args
  | ty :: ql, a :: qargs ->
    out a;
    (if ArgInt? ty then out "U" else ());
    out ", ";
    print_witness_args_as_c out ql qargs
  | _ -> ()

let print_witness_call_as_c_aux
  (out: (string -> ML unit))
  (validator_name: string)
  (arg_types: list arg_type)
  (witness_length: nat)
  (args: list string)
: ML unit
=
  out validator_name;
  out "(";
  print_witness_args_as_c out arg_types args;
  out "&context, &TestErrorHandler, witness, ";
  out (string_of_int witness_length);
  out ", 0);"

let print_witness_call_as_c
  (out: (string -> ML unit))
  (positive: bool)
  (validator_name: string)
  (arg_types: list arg_type)
  (witness_length: nat)
  (args: list string)
: ML unit
=
  out "
  {
    uint8_t context = 0;
    uint64_t output = ";
  print_witness_call_as_c_aux out validator_name arg_types witness_length args;
  out "
    printf(\"  ";
  print_witness_call_as_c_aux out validator_name arg_types witness_length args;
  out " // \");
    BOOLEAN result = !EverParseIsError(output);
    BOOLEAN consumes_all_bytes_if_successful = true;
    if (result) {
      consumes_all_bytes_if_successful = (output == ";
  out (string_of_int witness_length);
  out "U);
      result = consumes_all_bytes_if_successful;
    }
    if (result)
      printf (\"ACCEPTED\\n\\n\");
    else if (!consumes_all_bytes_if_successful)
      printf (\"REJECTED (not all bytes consumed)\\n\\n\");
    else
      printf (\"REJECTED (failed)\\n\\n\");
    if (";
  if positive then out "!";
  out "result)
      return 1;
  };
"

let print_witness_as_c_aux
  (out: (string -> ML unit))
  (witness: Seq.seq int)
  (len: int { len == Seq.length witness })
: ML unit
=
  out "  uint8_t witness[";
  out (string_of_int len);
  out "] = {";
  begin match Seq.seq_to_list witness with
  | [] -> ()
  | a :: q ->
    out (string_of_int a);
    List.iter (fun i -> out ", "; out (string_of_int i)) q
  end;
  out "};"

let print_witness_as_c_gen
  (out: (string -> ML unit))
  (witness: Seq.seq int)
  (f: (len: int { len == Seq.length witness }) -> ML unit)
: ML unit
= let len = Seq.length witness in
  out "{\n";
  print_witness_as_c_aux out witness len;
  out "
  printf(\"";
  print_witness_as_c_aux out witness len;
  out "\\n\");
";
  f len;
  out "};
"

let rec mk_args_as_file_name (accu: string) (l: list string) : Tot string
  (decreases l)
= match l with
  | [] -> accu
  | a :: q -> mk_args_as_file_name (accu ^ "." ^ a) q

let mk_output_filename
  (counter: ref int)
  (validator_name: string)
  (args: list string)
: ML string
= let i = !counter in
  counter := i + 1;
  mk_args_as_file_name ("witness." ^ string_of_int i ^ "." ^ validator_name) args ^ ".dat"

let print_witness_as_c
  (out: (string -> ML unit))
  (positive: bool)
  (validator_name: string)
  (arg_types: list arg_type)
  (counter: ref int)
  (witness: Seq.seq int)
  (args: list string)
: ML unit
= OS.write_witness_to_file (Seq.seq_to_list witness) (mk_output_filename counter ((if positive then "POS." else "NEG.") ^ validator_name) args);
  print_witness_as_c_gen out witness (fun len ->
    print_witness_call_as_c out positive validator_name arg_types len args
  )

let print_diff_witness_as_c
  (out: (string -> ML unit))
  (validator_name1: string)
  (validator_name2: string)
  (arg_types: list arg_type)
  (counter: ref int)
  (witness: Seq.seq int)
  (args: list string)
: ML unit
= OS.write_witness_to_file (Seq.seq_to_list witness) (mk_output_filename counter ("POS." ^ validator_name1 ^ ".NEG." ^ validator_name2) args);
  print_witness_as_c_gen out witness (fun len ->
    print_witness_call_as_c out true validator_name1 arg_types len args;
    print_witness_call_as_c out false validator_name2 arg_types len args
  )

let print_witness (witness: Seq.seq int) : ML unit =
  FStar.IO.print_string " produced witness: [";
  List.iter (fun i -> FStar.IO.print_string (string_of_int i); FStar.IO.print_string "; ") (Seq.seq_to_list witness);
  FStar.IO.print_string "]\n"

let rec mk_witness_call (accu: string) (l: list arg_type) (args: list string) : Tot string (decreases l) =
  match l, args with
  | ArgPointer :: q, _ -> mk_witness_call (Printf.sprintf "%s 0" accu) q args
  | _ :: ql, a :: qargs -> mk_witness_call (Printf.sprintf "%s %s" accu a) ql qargs
  | _ -> Printf.sprintf "(%s)" accu

let print_witness_and_call (name: string) (l: list arg_type) (witness: Seq.seq int) (args: list string) : ML unit =
  FStar.IO.print_string ";; call ";
  FStar.IO.print_string (mk_witness_call name l args);
  print_witness witness

let count_args (l: list arg_type) : Tot nat = List.Tot.length (List.Tot.filter (function ArgPointer -> false | _ -> true) l)

let rec want_witnesses (print_test_case: (Seq.seq int -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) (mk_want_another_witness: Seq.seq int -> list string -> Tot string) i : ML unit =
  z3.to_z3 "(check-sat)\n";
  let status = z3.from_z3 () in
  if status = "sat" then begin
    let witness = read_witness z3 in
    let witness_args = read_witness_args z3 [] nargs in
    print_witness_and_call name l witness witness_args;
    print_test_case witness witness_args;
    if i <= 1
    then ()
    else begin
      z3.to_z3 (mk_want_another_witness witness witness_args);
      want_witnesses print_test_case z3 name l nargs mk_want_another_witness (i - 1)
    end
  end
  else begin
    FStar.IO.print_string
      begin
        if status = "unsat"
        then";; unsat: no more witnesses"
        else if status = "unknown"
        then begin
          z3.to_z3 "(get-info :reason-unknown)";
          let msg = z3.from_z3 () in
          Printf.sprintf ";; unknown: %s" msg
        end
        else Printf.sprintf ";; %s: z3 gave up" status
      end;
    FStar.IO.print_newline ()
  end

let witnesses_for (print_test_case: (Seq.seq int -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) mk_get_first_witness mk_want_another_witness nbwitnesses =
  z3.to_z3 "(push)\n";
  z3.to_z3 mk_get_first_witness;
  want_witnesses print_test_case z3 name l nargs mk_want_another_witness nbwitnesses;
  z3.to_z3 "(pop)\n"

let rec mk_call_args (accu: string) (i: nat) (l: list arg_type) : Tot string (decreases l) =
  match l with
  | [] -> accu
  | ArgPointer :: q -> mk_call_args (Printf.sprintf "%s 0" accu) i q
  | _ :: q -> mk_call_args (Printf.sprintf "%s arg-%d" accu i) (i + 1) q

let rec mk_assert_args (accu: string) (i: nat) (l: list arg_type) : Tot string (decreases l) =
  match l with
  | [] -> accu
  | ArgPointer :: q -> mk_assert_args accu i q
  | ArgBool :: q -> mk_assert_args (Printf.sprintf "%s(declare-fun arg-%d () Bool)\n" accu i) (i + 1) q
  | ArgInt it :: q -> mk_assert_args (Printf.sprintf "%s(declare-fun arg-%d () Int)\n(assert (and (<= 0 arg-%d) (< arg-%d %d)))\n" accu i i i (pow2 (integer_type_bit_size it))) (i + 1) q

let mk_get_witness (name: string) (l: list arg_type) : string =
Printf.sprintf "
%s
(define-fun state-witness () State (%s initial-state))
(define-fun state-witness-input-size () Int (input-size state-witness))
(declare-fun state-witness-size () Int)
(assert (<= state-witness-size (choice-index state-witness)))
(assert (>= state-witness-size (choice-index state-witness)))
"
  (mk_assert_args "" 0 l)
  (mk_call_args name 0 l)

let mk_get_first_positive_test_witness (name: string) (l: list arg_type) : string =
  mk_get_witness name l ^ "
(assert (= (input-size state-witness) 0)) ; validator shall consume all input
"

let rec mk_choose_conj (witness: Seq.seq int) (accu: string) (i: nat) : Tot string
  (decreases (if i >= Seq.length witness then 0 else Seq.length witness - i))
= if i >= Seq.length witness
  then accu
  else mk_choose_conj witness ("(and (= (choose "^string_of_int i^") "^string_of_int (Seq.index witness i)^") "^accu^")") (i + 1)

let rec mk_arg_conj (accu: string) (i: nat) (l: list string) : Tot string (decreases l) =
  match l with
  | [] -> accu
  | arg :: q ->
    mk_arg_conj (Printf.sprintf "(and %s (= arg-%d %s))" accu i arg) (i + 1) q

let mk_want_another_distinct_witness witness witness_args : Tot string =
  Printf.sprintf
"(assert (not %s))
"
  (mk_arg_conj (mk_choose_conj witness ("(= (choice-index state-witness) "^string_of_int (Seq.length witness)^")") 0) 0 witness_args)

let mk_get_first_negative_test_witness (name: string) (l: list arg_type) : string =
  mk_get_witness name l ^
"
(assert (< state-witness-input-size 0)) ; validator shall genuinely fail, we are not interested in positive cases followed by garbage
"

let test_error_handler = "
static void TestErrorHandler (
  const char *typename_s,
  const char *fieldname,
  const char *reason,
  uint64_t error_code,
  uint8_t *context,
  EVERPARSE_INPUT_BUFFER input,
  uint64_t start_pos
) {
  (void) error_code;
  (void) input;
  if (*context) {
    printf(\"Reached from position %ld: type name %s, field name %s\\n\", start_pos, typename_s, fieldname);
  } else {
    printf(\"Parsing failed at position %ld: type name %s, field name %s. Reason: %s\\n\", start_pos, typename_s, fieldname, reason);
    *context = 1;
  }
}
"

let do_test (out_file: option string) (z3: Z3.z3) (prog: prog) (name1: string) (nbwitnesses: int) (pos: bool) (neg: bool) : ML unit =
  let args = List.assoc name1 prog in
  if None? args
  then failwith (Printf.sprintf "do_test: parser %s not found" name1);
  let args = Some?.v args in
  let modul, validator_name = module_and_validator_name name1 in
  let nargs = count_args args in with_option_out_file out_file (fun cout ->
  cout "#include <stdio.h>
#include <stdbool.h>
#include \"";
  cout modul;
  cout ".h\"
";
  cout test_error_handler;
  cout "
  int main(void) {
";
  let counter = alloc 0 in
  if pos
  then begin
    FStar.IO.print_string (Printf.sprintf ";; Positive test witnesses for %s\n" name1);
    witnesses_for (print_witness_as_c cout true validator_name args counter) z3 name1 args nargs (mk_get_first_positive_test_witness name1 args) mk_want_another_distinct_witness nbwitnesses
  end;
  if neg
  then begin
    FStar.IO.print_string (Printf.sprintf ";; Negative test witnesses for %s\n" name1);
    witnesses_for (print_witness_as_c cout false validator_name args counter) z3 name1 args nargs (mk_get_first_negative_test_witness name1 args) mk_want_another_distinct_witness nbwitnesses
  end;
  cout "  return 0;
  }
"
  )

let mk_get_first_diff_test_witness (name1: string) (l: list arg_type) (name2: string) : string =
  Printf.sprintf
"
%s
(assert (not (= (input-size (%s initial-state)) 0))) ; test cases that do not consume everything are considered failing
"
  (mk_get_first_positive_test_witness name1 l)
  (mk_call_args name2 0 l)

let do_diff_test_for (counter: ref int) (cout: string -> ML unit) (z3: Z3.z3) (prog: prog) name1 name2 args (nargs: nat { nargs == count_args args }) validator_name1 validator_name2 nbwitnesses =
  FStar.IO.print_string (Printf.sprintf ";; Witnesses that work with %s but not with %s\n" name1 name2);
  witnesses_for (print_diff_witness_as_c cout validator_name1 validator_name2 args counter) z3 name1 args nargs (mk_get_first_diff_test_witness name1 args name2) mk_want_another_distinct_witness nbwitnesses

let do_diff_test (out_file: option string) (z3: Z3.z3) (prog: prog) name1 name2 nbwitnesses =
  let args = List.assoc name1 prog in
  if None? args
  then failwith (Printf.sprintf "do_diff_test: parser %s not found" name1);
  let args = Some?.v args in
  let args2 = List.assoc name2 prog in
  if None? args2
  then failwith (Printf.sprintf "do_diff_test: parser %s not found" name2);
  if args2 <> Some args
  then failwith (Printf.sprintf "do_diff_test: parsers %s and %s do not have the same arg types" name1 name2);
  let nargs = count_args args in
  let modul1, validator_name1 = module_and_validator_name name1 in
  let modul2, validator_name2 = module_and_validator_name name2 in
  with_option_out_file out_file (fun cout ->
  cout "#include <stdio.h>
#include <stdbool.h>
#include \"";
  cout modul1;
  cout ".h\"
#include \"";
  cout modul2;
  cout ".h\"
";
  cout test_error_handler;
  cout "
  int main(void) {
";
  let counter = alloc 0 in
  do_diff_test_for counter cout z3 prog name1 name2 args nargs validator_name1 validator_name2 nbwitnesses;
  do_diff_test_for counter cout z3 prog name2 name1 args nargs validator_name2 validator_name1 nbwitnesses;
  cout "  return 0;
  }
"
)

let test_exe_mk_arg
  (accu: (int & string & string & string))
  (p: arg_type)
: Tot (int & string & string & string)
= let (cur_arg, read_args, call_args_lhs, call_args_rhs) = accu in
  let cur_arg_s = string_of_int cur_arg in
  let arg_var = "arg" ^ cur_arg_s in
  let cur_arg' = cur_arg + 1 in
  let read_args' = read_args ^
  begin match p with
  | ArgInt _ -> "
  unsigned long long "^arg_var^" = strtoull(argv["^cur_arg_s^"], NULL, 0);
"
  | ArgBool -> "
  BOOLEAN "^arg_var^" = (strcmp(argv["^cur_arg_s^"], \"true\") == 0);
  if (! ("^arg_var^" || strcmp(argv["^cur_arg_s^"], \"false\") == 0)) {
    printf(\"Argument %d must be true or false, got %s\\n\", "^cur_arg_s^", argv["^cur_arg_s^"]);
    return 1;
  }
"
  | _ -> "
unsigned long long "^arg_var^" = 0;
"
  end
  in
  let call_args_lhs' = call_args_lhs ^ arg_var ^ ", " in
  let call_args_rhs' = call_args_lhs ^ ", " ^ arg_var in
  (cur_arg', read_args', call_args_lhs', call_args_rhs')

let test_checker_c
  (modul: string)
  (validator_name: string)
  (params: list arg_type)
: Tot string
=
  let (nb_cmd_and_args, read_args, call_args_lhs, call_args_rhs) = List.Tot.fold_left test_exe_mk_arg (2, "", "", "") params in
  let nb_cmd_and_args_s = string_of_int nb_cmd_and_args in
  let nb_args_s = string_of_int (nb_cmd_and_args - 1) in
  "
#include \""^modul^".h\"
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <stdint.h>
#include <unistd.h>
#include <stdlib.h>

"^test_error_handler^"

int main(int argc, char** argv) {
  if (argc < "^nb_cmd_and_args_s^") {
    printf(\"Wrong number of arguments, expected "^nb_args_s^", got %d\\n\", argc);
    return 3;
  }
  char * filename = argv[1];
"^read_args^"
  int testfile = open(filename, O_RDONLY);
  if (testfile == -1) {
    printf(\"File %s does not exist\\n\", filename);
    return 3;
  }
  struct stat statbuf;
  if (fstat(testfile, &statbuf)) {
    close(testfile);
    printf(\"Cannot detect file size for %s\\n\", filename);
    return 3;
  }
  off_t len = statbuf.st_size;
  if (len > 4294967295) {
    printf(\"File is too large. EverParse/3D only supports data up to 4 GB\");
    return 3;
  }
  void * vbuf =
    mmap(NULL, len, PROT_READ, MAP_PRIVATE, testfile, 0);
  if (vbuf == MAP_FAILED) {
    close(testfile);
    printf(\"Cannot read %ld bytes from %s\\n\", len, filename);
    return 3;
  }
  uint8_t * buf = (uint8_t *) vbuf;
  printf(\"Read %ld bytes from %s\\n\", len, filename);
  uint8_t context = 0;
  uint64_t result = "^validator_name^"("^call_args_lhs^"&context, &TestErrorHandler, buf, len, 0);
  munmap(vbuf, len);
  close(testfile);
  if (EverParseIsError(result)) {
    printf(\"Witness from %s REJECTED because validator failed\\n\", filename);
    return 2;
  };
  if (result != (uint64_t) len) { // consistent with the postcondition of validate_with_action_t' (see also valid_length)
    printf(\"Witness from %s REJECTED because validator only consumed %ld out of %ld bytes\\n\", filename, result, len);
    return 1;
  }
  printf(\"Witness from %s ACCEPTED\\n\", filename);
  return 0;
}
"

let produce_test_checker_exe (out_file: string) (prog: prog) (name1: string) : ML unit =
  let args = List.assoc name1 prog in
  if None? args
  then failwith (Printf.sprintf "produce_test_checker_exe: parser %s not found" name1);
  let args = Some?.v args in
  let modul, validator_name = module_and_validator_name name1 in
  with_out_file out_file (fun cout ->
    cout (test_checker_c modul validator_name args)
  )
