module Z3TestGen
module Printf = FStar.Printf
open FStar.All
open FStar.Mul

module A = Ast
module T = Target
module I = InterpreterTarget

let mk_state:
  (input_size: string) ->
  (choice_index: string) ->
  (array_index: string) ->
  (next_array_index: string) ->
  (branch_index: string) ->
  Tot string
= Printf.sprintf "(mk-state %s %s %s %s %s)"

let choose:
  (array_index: string) ->
  (index: string) ->
  Tot string
= Printf.sprintf "(choose %s %s)"

let prelude : string =
"
(set-option :produce-models true)
(declare-datatypes () ((State "^mk_state "(input-size Int)" "(choice-index Int)" "(array-index Int)" "(next-array-index Int)" "(branch-index Int)" ^ ")))
(declare-datatypes () ((Result (mk-result (return-value Int) (after-state State)))))

; From EverParse3d.ErrorCode.is_range_okay
(define-fun is_range_okay ((size Int) (offset Int) (access_size Int)) Bool
  (and
    (>= size access_size)
    (>= (- size access_size) offset)
  )
)

(define-fun parse-empty ((x State)) Result
  (mk-result 0 x)
)

(declare-fun choose (Int Int) Int)
(assert (forall ((arr Int) (i Int))
  (and (<= 0 "^choose "arr" "i" ^ ") (< "^choose "arr" "i" ^ "256))
))

(declare-fun branch-trace (Int) Int)

(declare-fun probe-source-buffer (Int) Int)
(declare-fun probe-source-offset (Int) Int)
; TODO: we will also need a probe source size once we generalize the pointer type

(define-fun parse-false ((x State)) State
  " ^ mk_state "-1" "(choice-index x)" "(array-index x)" "(next-array-index x)" "(branch-index x)" ^ "
)

(define-fun parse-all-bytes ((x State)) State
  (if (<= (input-size x) 0)
    x
    " ^ mk_state "0" "(+ (choice-index x) (input-size x))" "(array-index x)" "(next-array-index x)" "(branch-index x)" ^ "
  )
)

(define-fun parse-all-zeros ((x State)) State
  (if (<= (input-size x) 0)
    x
    "^mk_state
      ("(if
        (forall ((j Int))
          (if (and (<= 0 j) (< j (input-size x)))
            (= "^choose "(array-index x)" "(+ (choice-index x) j)" ^" 0)
            true
          )
        )
        0
        -1
      )")
      "(+ (choice-index x) (input-size x))"
      "(array-index x)"
      "(next-array-index x)"
      "(branch-index x)"
    ^ "
  )
)

(define-fun parse-u8 ((x State)) Result
  (mk-result
    "^choose "(array-index x)" "(choice-index x)" ^ "
    (let ((new-size (- (input-size x) 1)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 1))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(define-fun parse-u16-be ((x State)) Result
  (mk-result
    (+ "^choose "(array-index x)" "(+ 1 (choice-index x))"^"
      ( * 256
        "^choose "(array-index x)" "(+ 0 (choice-index x))"^"
      )
    )
    (let ((new-size (- (input-size x) 2)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 2))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(define-fun parse-u16-le ((x State)) Result
  (mk-result
    (+ "^choose "(array-index x)" "(+ 0 (choice-index x))"^"
      ( * 256
        "^choose "(array-index x)" "(+ 1 (choice-index x))"^"
      )
    )
    (let ((new-size (- (input-size x) 2)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 2))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(define-fun parse-u32-be ((x State)) Result
  (mk-result
    (+ "^choose "(array-index x)" "(+ 3 (choice-index x))"^"
      ( * 256
        (+ "^choose "(array-index x)" "(+ 2 (choice-index x))"^"
          ( * 256
            (+ "^choose "(array-index x)" "(+ 1 (choice-index x))"^"
              ( * 256
                "^choose "(array-index x)" "(+ 0 (choice-index x))"^"
              )
            )
          )
        )
      )
    )
    (let ((new-size (- (input-size x) 4)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 4))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(define-fun parse-u32-le ((x State)) Result
  (mk-result
    (+ "^choose "(array-index x)" "(+ 0 (choice-index x))"^"
      ( * 256
        (+ "^choose "(array-index x)" "(+ 1 (choice-index x))"^"
          ( * 256
            (+ "^choose "(array-index x)" "(+ 2 (choice-index x))"^"
              ( * 256
                "^choose "(array-index x)" "(+ 3 (choice-index x))"^"
              )
            )
          )
        )
      )
    )
    (let ((new-size (- (input-size x) 4)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 4))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(define-fun parse-u64-be ((x State)) Result
  (mk-result
    (+ "^choose "(array-index x)" "(+ 7 (choice-index x))"^"
      ( * 256
        (+ "^choose "(array-index x)" "(+ 6 (choice-index x))"^"
          ( * 256
            (+ "^choose "(array-index x)" "(+ 5 (choice-index x))"^"
              ( * 256
                (+ "^choose "(array-index x)" "(+ 4 (choice-index x))"^"
                  ( * 256
                    (+ "^choose "(array-index x)" "(+ 3 (choice-index x))"^"
                      ( * 256
                        (+ "^choose "(array-index x)" "(+ 2 (choice-index x))"^"
                          ( * 256
                            (+ "^choose "(array-index x)" "(+ 1 (choice-index x))"^"
                              ( * 256
                                "^choose "(array-index x)" "(+ 0 (choice-index x))"^"
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
    (let ((new-size (- (input-size x) 8)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 8))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(define-fun parse-u64-le ((x State)) Result
  (mk-result
    (+ "^choose "(array-index x)" "(+ 0 (choice-index x))"^"
      ( * 256
        (+ "^choose "(array-index x)" "(+ 1 (choice-index x))"^"
          ( * 256
            (+ "^choose "(array-index x)" "(+ 2 (choice-index x))"^"
              ( * 256
                (+ "^choose "(array-index x)" "(+ 3 (choice-index x))"^"
                  ( * 256
                    (+ "^choose "(array-index x)" "(+ 4 (choice-index x))"^"
                      ( * 256
                        (+ "^choose "(array-index x)" "(+ 5 (choice-index x))"^"
                          ( * 256
                            (+ "^choose "(array-index x)" "(+ 6 (choice-index x))"^"
                              ( * 256
                                "^choose "(array-index x)" "(+ 7 (choice-index x))"^"
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
    (let ((new-size (- (input-size x) 8)))
      " ^ mk_state
        "(if (< new-size 0)
          -1
          new-size
        )"
        "(+ (choice-index x) (if (< new-size 0) (input-size x) 8))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
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

;; see EverParse3d.Actions.Base.validate_nlist_total_constant_size
(define-fun parse-nlist-total-constant-size ((size Int) (eltSize Int) (x State)) State
  (if (< (input-size x) 0)
    x
    (if (and (= 0 (mod size eltSize)) (>= (input-size x) size))
      " ^  mk_state
        "(- (input-size x) size)"
        "(+ (choice-index x) size)"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
      " ^ mk_state
        "-1"
        "(+ (choice-index x) (input-size x))"
        "(array-index x)"
        "(next-array-index x)"
        "(branch-index x)"
      ^ "
    )
  )
)

(declare-fun state-witness-size (Int) Int)
(assert (forall ((x Int)) (>= (state-witness-size x) 0)))
(define-fun initial-state () State " ^ mk_state "(state-witness-size 0)" "0" "0" "1" "0" ^ ")

"

let mk_constant = function
  | A.Unit -> "0"
  | A.Int _ x -> string_of_int x
  | A.XInt _ x -> string_of_int (OS.int_of_string x)
  | A.Bool true -> "true"
  | A.Bool false -> "false"
  | A.String s -> "0"

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

let ident_to_string = A.ident_to_string

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
  | T.ProbeFunctionName s -> mk_app (ident_to_string s)

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

let mk_app_without_paren' id args =
  mk_args_aux None id args

let mk_app_without_paren id args =
  mk_app_without_paren' (ident_to_string id) args
  
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
  | I.DT_App _ _ hd args -> parse_readable_app hd args

let parse_not_readable_app'
  (hd: string)
  (args: list I.expr)
: Tot (parser not_reading)
= maybe_toplevel_parser (fun _ _ _ _ -> { call = mk_app_without_paren' hd args })

let parse_not_readable_app
  (hd: A.ident)
  (args: list I.expr)
: Tot (parser not_reading)
= parse_not_readable_app' (ident_to_string hd) args

let parse_dtyp
  (d: I.dtyp)
: Tot (parser not_reading)
= if I.allow_reader_of_dtyp d
  then wrap_parser (parse_readable_dtyp d)
  else match d with
    | I.DT_IType i -> parse_itype i
    | I.DT_App _ _ hd args -> parse_not_readable_app hd args

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
         (if (or (< (branch-index (after-state "^tmp^")) 0) (= (branch-trace (branch-index (after-state "^tmp^"))) 0))
           (let (("^dsnd_binder_name^" (return-value "^tmp^")))
             ("^dsnd^"
               "^mk_state
                 ("(input-size (after-state "^tmp^"))")
                 ("(choice-index (after-state "^tmp^"))")
                 ("(array-index (after-state "^tmp^"))")
                 ("(next-array-index (after-state "^tmp^"))")
                 ("(+ (if (< (branch-index (after-state "^tmp^")) 0) 0 1) (branch-index (after-state "^tmp^")))")
               ^"
             )
           )
           "^mk_state
             "-2"
             ("(choice-index (after-state "^tmp^"))")
             ("(array-index (after-state "^tmp^"))")
             ("(next-array-index (after-state "^tmp^"))")
             ("(+ 1 (branch-index (after-state "^tmp^")))")
           ^"
         )
         "^mk_state
           ("(if (or (< (branch-index (after-state "^tmp^")) 0) (= (branch-trace (branch-index (after-state "^tmp^"))) 1)) -1 -2)")
           ("(choice-index (after-state "^tmp^"))")
           ("(array-index (after-state "^tmp^"))")
           ("(next-array-index (after-state "^tmp^"))")
           ("(+ (if (< (branch-index (after-state "^tmp^")) 0) 0 1) (branch-index (after-state "^tmp^")))")
         ^"
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

let mk_parse_dep_pair
  (name: string)
  (binders: string)
  (dfst: string)
  (dsnd_binder_name: string)
  (dsnd: string) (* already contains the new argument *)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (let (("^tmp^" ("^dfst^" "^input^")))
     (if (< (input-size (after-state "^tmp^")) 0)
       (after-state "^tmp^")
       (let (("^dsnd_binder_name^" (return-value "^tmp^")))
         ("^dsnd^" (after-state "^tmp^"))
       )
     )
   )
 )
"

let parse_dep_pair (tag: parser reading) (payload_binder: A.ident) (payload: parser not_reading) : parser not_reading =
  fun name binders _ out ->
    let payload_binder = ident_to_string payload_binder in
    let name_tag = Printf.sprintf "%s-tag" name in
    let body_tag = tag name_tag binders false out in
    let binders' = push_binder payload_binder "Int" binders in (* TODO: support more types *)
    let name_payload = Printf.sprintf "%s-payload" name in
    let body_payload = payload name_payload binders' false out in
    out (mk_parse_dep_pair name binders.bind body_tag.call payload_binder body_payload.call);
    { call = mk_function_call name binders }

let parse_refine (tag: parser reading) (cond_binder: A.ident) (cond: unit -> ML string) : parser not_reading =
  parse_dep_pair_with_refinement tag cond_binder cond cond_binder (parse_itype I.Unit)

let mk_parse_ifthenelse_cons
  (counter: int)
  (name: string)
  (binders: string)
  (cond: string)
  (f_then: string)
  (f_else: string)
: string
= let input = Printf.sprintf "%s-input" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (if (and "^cond^" (or (< (branch-index "^input^") 0) (= (branch-trace (branch-index "^input^")) "^string_of_int counter^")))
     ("^f_then^" (if (< (branch-index "^input^") 0) "^input^" "^mk_state ("(input-size "^input^")") ("(choice-index "^input^")") ("(array-index "^input^")") ("(next-array-index "^input^")") ("(+ 1 (branch-index "^input^"))")^"))
     (if (not "^cond^")
       ("^f_else^" "^input^")
       "^mk_state "-2" ("(choice-index "^input^")") ("(array-index "^input^")") ("(next-array-index "^input^")") ("(+ (if (< (branch-index "^input^") 0) 0 1) (branch-index "^input^"))") ^ " ; this is a Z3 encoding artifact, not a parsing failure
     )
   )
 )
"

let parse_ifthenelse_cons (cond: unit -> ML string) (pthen: parser not_reading) (pelse: int -> parser not_reading) (counter: int) : parser not_reading =
  fun name binders _ out ->
    let name_then = Printf.sprintf "%s-then" name in
    let body_then = pthen name_then binders false out in
    let name_else = Printf.sprintf "%s-else" name in
    let body_else = pelse (counter + 1) name_else binders false out in
    out (mk_parse_ifthenelse_cons counter name binders.bind (cond ()) body_then.call body_else.call);
    { call = mk_function_call name binders }

let mk_parse_ifthenelse_nil
  (counter: int)
  (name: string)
  (binders: string)
  (cond: string)
  (f_then: string)
  (f_else: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (let (("^tmp^" (if (< (branch-index "^input^") 0) "^input^" "^mk_state ("(input-size "^input^")") ("(choice-index "^input^")") ("(array-index "^input^")") ("(next-array-index "^input^")") ("(+ 1 (branch-index "^input^"))") ^ ")))
     (if (and "^cond^" (or (< (branch-index "^input^") 0) (= (branch-trace (branch-index "^input^")) "^string_of_int counter^")))
       ("^f_then^" "^tmp^")
       (if (and (not "^cond^") (or (< (branch-index "^input^") 0) (= (branch-trace (branch-index "^input^")) "^string_of_int (1 + counter)^")))
         ("^f_else^" "^tmp^")
         "^mk_state "-2" ("(choice-index "^tmp^")") ("(array-index "^tmp^")") ("(next-array-index "^tmp^")") ("(+ (if (< (branch-index "^input^") 0) 0 1) (branch-index "^input^"))") ^ " ; this is a Z3 encoding artifact, not a parsing failure
       )
     )
   )
 )
"

let parse_ifthenelse_nil (cond: unit -> ML string) (pthen: parser not_reading) (pelse: parser not_reading) (counter: int) : parser not_reading =
  fun name binders _ out ->
    let name_then = Printf.sprintf "%s-then" name in
    let body_then = pthen name_then binders false out in
    let name_else = Printf.sprintf "%s-else" name in
    let body_else = pelse name_else binders false out in
    out (mk_parse_ifthenelse_nil counter name binders.bind (cond ()) body_then.call body_else.call);
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
      "^mk_state "-1" ("(choice-index "^input^")") ("(array-index "^input^")") ("(next-array-index "^input^")") ("(branch-index "^input^")") ^ "
      (let (("^res^" ("^body^" "^mk_state sz ("(choice-index "^input^")") ("(array-index "^input^")") ("(next-array-index "^input^")") ("(branch-index "^input^")")^")))
        " ^ mk_state
          ("(if (= (input-size "^res^") 0)
            (- (input-size "^input^") "^sz^")
            (if (> (input-size "^res^") 0)
              -1
              (input-size "^res^")
            )
          )")
          ("(choice-index "^res^")")
          ("(array-index "^res^")")
          ("(next-array-index "^res^")") 
          ("(branch-index "^res^")")
        ^"
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

let itype_byte_size (i: I.itype) : Tot (option pos) = match i with
  | I.UInt8 | I.UInt8BE -> Some 1
  | I.UInt16 | I.UInt16BE -> Some 2
  | I.UInt32 | I.UInt32BE -> Some 4
  | I.UInt64 | I.UInt64BE -> Some 8
  | _ -> None

let parse_nlist_total_constant_size
  (i: I.itype {Some? (itype_byte_size i)}) // TODO: DT_App?
  (size: I.expr)
: Tot (parser not_reading)
= parse_not_readable_app'
    "parse-nlist-total-constant-size"
    [
      size;
      T.mk_expr (T.Constant (A.Int A.UInt8 (Some?.v (itype_byte_size i))));
    ]

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
      "^mk_state "-1" ("(choice-index (after-state "^tmp^"))") ("(array-index (after-state "^tmp^"))") ("(next-array-index (after-state "^tmp^"))") ("(branch-index (after-state "^tmp^"))") ^ "
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

let mk_parse_probe
  (name: string)
  (binders: string)
  (body: string)
  (size: string)
: Tot string
= let input = Printf.sprintf "%s-input" name in
  let sz = Printf.sprintf "%s-size" name in
  let res = Printf.sprintf "%s-res" name in
  let ptr = Printf.sprintf "%s-tmpptr" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
  (let (("^ptr^" (parse-u64-le "^input^"))) ; FIXME: generalize to user-specified pointer value type
    (if (< (input-size (after-state "^ptr^")) 0)
      (after-state "^ptr^")
      (if
        (and
          (and
            (= (return-value "^ptr^") (next-array-index (after-state "^ptr^"))) ; we always constrain Z3 to produce a test case with correct probe pointers
            (= (state-witness-size (next-array-index (after-state "^ptr^"))) "^size^") ; we always constrain Z3 to produce probe buffers whose size is equal to the user-specified probe size
          )
          (and ; record the location where the probe pointer is stored
            (= (probe-source-buffer (next-array-index (after-state "^ptr^"))) (array-index "^input^"))
            (= (probe-source-offset (next-array-index (after-state "^ptr^"))) (choice-index "^input^"))
          )
        )
        (let (("^tmp^" ("^body^" "^
          mk_state
            ("(state-witness-size (next-array-index (after-state "^ptr^")))")
            "0"
            ("(next-array-index (after-state "^ptr^"))")
            ("(+ 1 (next-array-index (after-state "^ptr^")))")
            ("(branch-index (after-state "^ptr^"))")
          ^")))
          "^mk_state // NOTE: we follow EverParse3d.Actions.Base.probe_then_validate, which DOES NOT check whether everything was consumed
            ("(if (< (input-size "^tmp^") 0) (input-size "^tmp^") (input-size (after-state "^ptr^")))")
            ("(choice-index (after-state "^ptr^"))")
            ("(array-index (after-state "^ptr^"))")
            ("(next-array-index "^tmp^")")
            ("(branch-index "^tmp^")")
          ^"
        )
        "^mk_state
          "-2"
          ("(choice-index (after-state "^ptr^"))")
          ("(array-index (after-state "^ptr^"))")
          ("(next-array-index (after-state "^ptr^"))")
          ("(branch-index (after-state "^ptr^"))")
        ^"
      )
    )
  )
)
"

let parse_probe
  (size: unit -> ML string)
  (body: parser not_reading)
: Tot (parser not_reading)
= fun name binders _ out ->
    let body_name = Printf.sprintf "%s-body" name in
    let body = body body_name binders false out in
    out (mk_parse_probe name binders.bind body.call (size ()));
    { call = mk_function_call name binders }

let rec typ_depth (t: I.typ) : GTot nat
  (decreases t)
= match t with
  | I.T_if_else _ t1 t2 // 2 accounts for the call to parse_then_else_with_branch_trace
    -> 2 + typ_depth t1 + typ_depth t2
  | I.T_pair _ _ t1 _ t2
    -> 1 + typ_depth t1 + typ_depth t2
  | I.T_dep_pair _ _ (_, t')
  | I.T_dep_pair_with_action _ _ (_, t') _
  | I.T_dep_pair_with_refinement _ _ _ (_, t')
  | I.T_dep_pair_with_refinement_and_action _ _ _ (_, t') _
  | I.T_with_action _ t' _
  | I.T_drop t'
  | I.T_with_comment _ t' _
  | I.T_at_most _ _ t'
  | I.T_exact _ _ t'
  | I.T_nlist _ _ _ t'
    -> 1 + typ_depth t'
  | I.T_with_dep_action _ _ _
  | I.T_refine _ _ _
  | I.T_refine_with_action _ _ _ _
  | I.T_false _
  | I.T_string _ _ _
  | I.T_denoted _ _
  | I.T_probe_then_validate _ _ _ _ _ _ _ _ _
    -> 0

let rec parse_typ (t : I.typ) : Tot (parser not_reading)
  (decreases (typ_depth t))
= 
  match t with
  | I.T_false _ -> parse_false
  | I.T_with_dep_action _ d _
  | I.T_denoted _ d -> parse_denoted d
  | I.T_pair _ _ t1 _ t2 -> parse_pair (parse_typ t1) (parse_typ t2)
  | I.T_dep_pair_with_action _ t1 (lam, t2) _
  | I.T_dep_pair _ t1 (lam, t2) -> parse_dep_pair (parse_readable_dtyp t1) lam (parse_typ t2)
  | I.T_refine_with_action _ base (lam, cond) _
  | I.T_refine _ base (lam, cond) -> parse_refine (parse_readable_dtyp base) lam (fun _ -> mk_expr cond)
  | I.T_dep_pair_with_refinement_and_action _ base (lam_cond, cond) (lam_k, k) _
  | I.T_dep_pair_with_refinement _ base (lam_cond, cond) (lam_k, k) -> parse_dep_pair_with_refinement (parse_readable_dtyp base) lam_cond (fun _ -> mk_expr cond) lam_k (parse_typ k)
  | I.T_if_else cond t1 t2 -> parse_ifthenelse cond t1 t2 0
  | I.T_with_action _ base _
  | I.T_drop base
  | I.T_with_comment _ base _ -> parse_typ base
  | I.T_at_most _ size body -> parse_at_most (fun _ -> mk_expr size) (parse_typ body)
  | I.T_exact _ size body -> parse_exact (fun _ -> mk_expr size) (parse_typ body)
  | I.T_string _ elt terminator -> parse_string (parse_readable_dtyp elt) (fun _ -> mk_expr terminator)
  | I.T_nlist _ _ size body ->
    if match body with
    | I.T_denoted _ (I.DT_IType i) -> Some? (itype_byte_size i)
    | _ -> false
    then
      let I.T_denoted _ (I.DT_IType i) = body in
      parse_nlist_total_constant_size i size
    else
      parse_nlist (fun _ -> mk_expr size) (parse_typ body)
  | I.T_probe_then_validate _fn body _ptr_sz _nullable _probe _dest _as_u64 _probe_init dest_sz -> 
    parse_probe (fun _ -> mk_expr dest_sz) (parse_denoted body)

and parse_ifthenelse (cond: I.expr) (tthen: I.typ) (telse: I.typ) : Tot (int -> parser not_reading)
  (decreases (1 + typ_depth tthen + typ_depth telse))
= match telse with
  | I.T_if_else cond2 tthen2 telse2 ->
    parse_ifthenelse_cons (fun _ -> mk_expr cond) (parse_typ tthen) (parse_ifthenelse cond2 tthen2 telse2)
  | _ ->
    parse_ifthenelse_nil (fun _ -> mk_expr cond) (parse_typ tthen) (parse_typ telse)

type simple_arg_type (allow_out: bool) =
| ArgInt of A.integer_type
| ArgBool
| ArgOutput: squash allow_out -> string -> simple_arg_type allow_out
| ArgExtern: squash allow_out -> simple_arg_type allow_out

type arg_type =
| ArgSimple of simple_arg_type false
| ArgPointer of simple_arg_type true
| ArgCopyBuffer // for probe destination buffers

let output_type_name_to_string (i: A.ident) : Tot string = ident_to_string i

let simple_arg_type_of_typ (t: T.typ) (allow_out: bool) : Tot (option (simple_arg_type allow_out)) =
  match t with
  | T.T_app {v = {modul_name = None; name = "Bool"}} _ _
    -> Some ArgBool
  | T.T_app i k _
    ->
    begin match A.maybe_as_integer_typ i with
    | Some t -> Some (ArgInt t)
    | None ->
      if A.KindOutput? k && allow_out then Some (ArgOutput () (output_type_name_to_string i))
      else if A.KindExtern? k && allow_out then Some (ArgExtern ())
      else None
    end
  | _ -> None

let arg_type_of_typ (t: T.typ) : Tot (option arg_type) =
  match t with
  | T.T_pointer t _ ->
    begin match simple_arg_type_of_typ t true with
    | Some t' -> Some (ArgPointer t')
    | _ -> None
    end
  | T.T_app {v = {modul_name = None; name = "EVERPARSE_COPY_BUFFER_T"}} _ _
    -> Some ArgCopyBuffer
  | T.T_app {v = {modul_name = None; name = "PUINT8"}} _ _
    -> Some (ArgPointer (ArgInt A.UInt8))
  | _ ->
    begin match simple_arg_type_of_typ t false with
    | Some t' -> Some (ArgSimple t')
    | _ -> None
    end

let smt_type_of_typ (t: T.typ) : Tot string =
  match arg_type_of_typ t with
  | Some (ArgSimple ArgBool) -> "Bool"
  | Some ArgCopyBuffer
  | Some (ArgSimple _)
  | Some (ArgPointer _)
  | None
    -> "Int"

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
  | T.Probe_function _ _ _
  | T.Output_type _
  | T.Output_type_expr _ _
  | T.Extern_type _
  | T.Extern_fn _ _ _ _
  | T.Extern_probe _ _
  -> ()

type prog_def =
| ProgDef:
  args: list (string & arg_type) ->
  enum_base_type: option arg_type ->
  prog_def
| ProgOutput:
  args: list (string & simple_arg_type true) ->
  prog_def
| ProgProbe:
  T.probe_qualifier ->
  prog_def

let prog = list (string & prog_def)

let rec arg_type_of_typ_with_prog
  (accu: prog)
  (t: T.typ)
: Tot (option arg_type)
  (decreases t)
= match arg_type_of_typ t with
  | Some ty -> Some ty
  | None ->
    begin match t with
    | T.T_app hd _ _ ->
      begin match List.Tot.assoc (ident_to_string hd) accu with
      | Some (ProgDef args enum_base_type) -> enum_base_type
      | _ -> None
      end
    | T.T_with_action base _
    | T.T_with_dep_action base _
    | T.T_with_comment base _
    | T.T_refine base _ ->
      arg_type_of_typ_with_prog accu base
    | _ -> None
    end

let produce_type_decl (out: string -> ML unit) (accu: prog) (a: I.type_decl) : ML prog =
  let binders = binders_of_params a.name.td_params in
  let name = ident_to_string a.name.td_name in
  let _ = parse_typ a.typ name binders true out in
  (name, ProgDef
    (List.map (fun (i, ty) -> match arg_type_of_typ_with_prog accu ty with Some t -> (ident_to_string i, t) | None -> failwith (Printf.sprintf "Parser %s has unsupported argument type for %s" name (ident_to_string i))) a.name.td_params)
    begin match a.enum_typ with
    | Some ty -> arg_type_of_typ_with_prog accu ty
    | _ -> None
    end
  ) :: accu

let simple_arg_type_of_ast_typ
  (a: Ast.typ)
: Tot (simple_arg_type true)
= match a.v with
  | A.Pointer _ _ -> ArgExtern ()
  | A.Type_app i _ _ _->
    begin match A.maybe_as_integer_typ i with
    | Some it -> ArgInt it
    | None ->
      if None? i.v.modul_name && i.v.name = "Bool"
      then ArgBool
      else ArgOutput () (output_type_name_to_string i)
    end
  | A.Type_arrow _ _ -> ArgExtern() //Exclude this case somehow?

let rec prog_out_fields_of_ast_out_fields
  (accu: list (string & simple_arg_type true))
  (fds: list A.out_field)
: Tot (list (string & simple_arg_type true))
  (decreases fds)
= match fds with
  | [] -> List.Tot.rev accu
  | A.Out_field_named name ty None :: q ->
    prog_out_fields_of_ast_out_fields
      ((ident_to_string name, simple_arg_type_of_ast_typ ty) :: accu)
      q
  | _ :: q -> prog_out_fields_of_ast_out_fields accu q

let produce_output_type_decl
  (accu: prog)
  (ot: A.out_typ)
: Tot prog
= (ident_to_string ot.out_typ_names.typedef_name, ProgOutput (prog_out_fields_of_ast_out_fields [] ot.out_typ_fields)) :: accu

let produce_probe_decl (accu: prog) (probe: A.ident) pq : Tot prog =
    let name = probe.v.name in // ignore module qualifier
    let x = (name, ProgProbe pq) in
    if List.Tot.mem x accu
    then accu
    else x :: accu

let produce_decl (out: string -> ML unit) (accu: prog) (a: I.decl) : ML prog =
  match a with
  | Inl (T.Output_type ot, _) -> produce_output_type_decl accu ot
  | Inl (T.Extern_probe probe pq, _) -> produce_probe_decl accu probe pq
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

let read_witness_layer (z3: Z3.z3) (array_index: nat) : ML (Seq.seq int) =
  let array_index_s = string_of_int array_index in
  z3.to_z3 (Printf.sprintf "(eval (state-witness-size %s))\n" array_index_s);
  let witness_size = Lisp.read_bare_int_from z3.from_z3 in
  let rec aux (accu: Seq.seq int) (remaining: int) : ML (Seq.seq int) =
    if remaining <= 0
    then accu
    else
      let index = remaining - 1 in
      let _ = z3.to_z3 (Printf.sprintf "(eval %s)\n" (choose array_index_s (string_of_int index))) in
      let v = Lisp.read_bare_int_from z3.from_z3 in
      aux (Seq.cons v accu) index
  in
  aux Seq.empty witness_size

let read_witness (use_ptr: bool) (z3: Z3.z3) : ML (Seq.seq (Seq.seq int) & option (Seq.seq (int & int))) =
  z3.to_z3 "(eval (next-array-index state-witness))\n";
  let nb_layers = Lisp.read_bare_int_from z3.from_z3 in
  if nb_layers < 1
  then failwith "read_witness: impossible: less than 1 layer";
  let rec aux (accu: Seq.seq (Seq.seq int)) (remaining: nat) : ML (Seq.seq (Seq.seq int)) =
    if remaining = 0
    then accu
    else
      let layer = remaining - 1 in
      let wl = read_witness_layer z3 layer in
      let accu' = Seq.cons wl accu in
      aux accu' layer
  in
  let layers = aux Seq.empty nb_layers in
  if use_ptr
  then
    let rec aux2 (accu: Seq.seq (int & int)) (layer: nat) : ML (Seq.seq (int & int)) =
      if layer = 0
      then accu
      else begin
        z3.to_z3 (Printf.sprintf "(eval (probe-source-buffer %d))\n" layer);
        let buf = Lisp.read_bare_int_from z3.from_z3 in
        z3.to_z3 (Printf.sprintf "(eval (probe-source-offset %d))\n" layer);
        let off = Lisp.read_bare_int_from z3.from_z3 in
        let accu' = Seq.cons (buf, off) accu in
        let layer' : nat = layer - 1 in
        aux2 accu' layer'
      end
    in
    (layers, Some (aux2 Seq.empty (nb_layers - 1)))
  else (layers, None)

let read_branch_trace (z3: Z3.z3) : ML (Seq.seq int) =
  z3.to_z3 "(eval (branch-index state-witness))\n";
  let witness_size = Lisp.read_bare_int_from z3.from_z3 in
  let rec aux (accu: Seq.seq int) (remaining: int) : ML (Seq.seq int) =
    if remaining <= 0
    then accu
    else
      let index = remaining - 1 in
      let _ = z3.to_z3 (Printf.sprintf "(eval (branch-trace %d))\n" index) in
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
  (l: list (string & arg_type)) (args: list string)
: ML unit
= match l, args with
  | (name, ArgCopyBuffer) :: q, _
  | (name, ArgPointer _) :: q, _ ->
    out name;
    out ", ";
    print_witness_args_as_c out q args
  | (_, ArgSimple ty) :: ql, a :: qargs ->
    out a;
    (if ArgInt? ty then out "U" else ());
    out ", ";
    print_witness_args_as_c out ql qargs
  | _, []
  | [], _
    -> ()

let out_witness_len
  (out: (string -> ML unit))
  (flight: string)
  (num: nat)
: ML unit
= out "witness";
  out flight;
  out (string_of_int num);
  out "[0].len"

let print_witness_call_as_c_aux
  (out: (string -> ML unit))
  (flight: string)
  (validator_name: string)
  (arg_types: list (string & arg_type))
  (args: list string)
  (num: nat)
: ML unit
=
  out validator_name;
  out "(";
  print_witness_args_as_c out arg_types args;
  out "&context, &TestErrorHandler, witness";
  out flight;
  out (string_of_int num);
  out "[0].buf, ";
  out_witness_len out flight num;
  out ", 0);"

let pointer_elt_type_as_c (x: simple_arg_type true) : Tot (option string) =
  match x with
  | ArgInt A.UInt8 -> Some "uint8_t"
  | ArgInt A.UInt16 -> Some "uint16_t"
  | ArgInt A.UInt32 -> Some "uint32_t"
  | ArgInt A.UInt64 -> Some "uint64_t"
  | ArgBool -> Some "BOOLEAN"
  | ArgOutput _ s -> Some s
  | _ -> None

let alloc_ptr_arg
  (arg_var: string)
  (pt: simple_arg_type true)
: Tot string
=
    match pointer_elt_type_as_c pt with
    | None ->
"
  void * "^arg_var^" = NULL;
"
    | Some ty ->
Printf.sprintf "
  %s _contents_%s;
  %s *%s = &_contents_%s;
  memset((void*)%s, 0, sizeof(%s));
"
  ty arg_var
  ty arg_var arg_var
  arg_var ty

let rec print_outparameter
  (#allow_out: bool)
  (out: (string -> ML unit))
  (p: prog)
  (expr: string)
  (ty: simple_arg_type allow_out)
: ML unit
= match ty with
  | ArgBool
  | ArgInt _ ->
    out "
  printf(\"// ";
    out expr;
    out " = %\" PRIu64 \"\\n\", ((uint64_t) (";
    out expr;
    out ")));\n"
  | ArgExtern _ -> ()
  | ArgOutput _ name ->
    begin match List.Tot.assoc name p with
    | Some (ProgOutput args) ->
      List.iter
        (fun (fd, ty) ->
          print_outparameter out p (expr ^ "." ^ fd) ty
        )
        args
    | _ -> ()
    end

let print_outparameters
  (out: (string -> ML unit))
  (p: prog)
  (arg_types: list (string & arg_type))
: ML unit
= List.iter
    (fun (name, ty) ->
      match ty with
      | ArgPointer ty -> print_outparameter out p ("(*" ^ name ^ ")") ty
      | ArgCopyBuffer
      | ArgSimple _ -> ()
    )
    arg_types

let alloc_default_copy_buffer
  (flight: string)
  (wid: nat)
  (nblayers: nat)
  (arg_var: string)
: Tot string
=
  Printf.sprintf
"
  copy_buffer_t _contents_%s = { .layers = witness%s%d, .count = %d, .cur = 0U };
  EVERPARSE_COPY_BUFFER_T %s = (void* ) &_contents_%s;
"
  arg_var
  flight
  wid
  nblayers
  arg_var
  arg_var

let alloc_ptr_copy_buffer
  (flight: string)
  (wid: nat)
  (arg_var: string)
: Tot string
=
  Printf.sprintf
"
  copy_buffer_t _contents_%s = witness%s%d[0];
  EVERPARSE_COPY_BUFFER_T %s = (void* ) &_contents_%s;
"
  arg_var
  flight
  wid
  arg_var
  arg_var

let alloc_copy_buffer
  (use_ptr: bool)
  (flight: string)
  (wid: nat)
  (nblayers: nat)
  (arg_var: string)
: Tot string
=
  if use_ptr
  then alloc_ptr_copy_buffer flight wid arg_var
  else alloc_default_copy_buffer flight wid nblayers arg_var

let print_witness_call_as_c
  (use_ptr: bool)
  (out: (string -> ML unit))
  (p: prog)
  (positive: bool)
  (flight: string)
  (validator_name: string)
  (arg_types: list (string & arg_type))
  (args: list string)
  (num: nat)
  (nblayers: nat)
: ML unit
=
  out "
  {
    uint8_t context = 0;
";
  List.iter
    (fun arg_ty ->
      match arg_ty with
      | (arg_var, ArgCopyBuffer) -> out (alloc_copy_buffer use_ptr flight num nblayers arg_var)
      | (arg_var, ArgPointer ty) -> out (alloc_ptr_arg arg_var ty)
      | (_, ArgSimple _) -> ()
    )
    arg_types;
  out "
    uint64_t output = ";
  print_witness_call_as_c_aux out flight validator_name arg_types args num;
  out "
    printf(\"  // ";
  print_witness_call_as_c_aux out flight validator_name arg_types args num;
  out " // \");
    BOOLEAN result = !EverParseIsError(output);
    BOOLEAN consumes_all_bytes_if_successful = true;
    if (result) {
      consumes_all_bytes_if_successful = (output == ";
  out_witness_len out flight num;
  out ");
      result = consumes_all_bytes_if_successful;
    }
    if (result) {
      printf (\"ACCEPTED\\n\");
";
  print_outparameters out p arg_types;
  out
"
      printf (\"\\n\");
    }
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

let print_witness_layer_as_c_aux
  (out: (string -> ML unit))
  (flight: string)
  (witness: Seq.seq int)
  (len: int { len == Seq.length witness })
  (num: nat)
  (lid: int)
: ML string
=
  let layer_name = "witness" ^ flight ^ string_of_int num ^ "_" ^ string_of_int lid in
  out "  uint8_t ";
  if len > 0
  then begin
    out layer_name;
    out "[";
    out (string_of_int len);
    out "] = {";
    begin match Seq.seq_to_list witness with
    | [] -> ()
    | a :: q ->
      out (string_of_int a);
      List.iter (fun i -> out ", "; out (string_of_int i)) q
    end;
    out "};"
  end
  else begin
    out "*";
    out layer_name;
    out " = NULL;"
  end;
  layer_name

let print_witness_as_c_aux
  (out: (string -> ML unit))
  (print_c_initializer: bool)
  (flight: string)
  (witness: Seq.seq (Seq.seq int))
  (pointer_locs: option (Seq.seq (int & int)))
  (len: int { len == Seq.length witness })
  (num: nat)
: ML unit
=
  let rec aux accu (i: nat) : ML string =
    if i >= len
    then accu
    else begin
      let w = Seq.index witness i in
      let wlen = Seq.length w in
      let layer_name = print_witness_layer_as_c_aux out flight w wlen num i in
      let layer = Printf.sprintf "{ %s%s, %s%d }"
        (if print_c_initializer then ".buf = " else "")
        layer_name
        (if print_c_initializer then ".len = " else "")
        wlen
      in
      let accu' =
        if accu = ""
        then layer
        else accu ^ "," ^ layer
      in
      aux accu' (i + 1)
    end
  in
  let layers = aux "" 0 in
  out "  witness_layer_t witness";
  out flight;
  out (string_of_int num);
  out "[";
  out (string_of_int len);
  out "] = {";
  out layers;
  out "};";
  match pointer_locs with
  | None -> ()
  | Some pl ->
    let rec aux2 (layer: nat) : ML unit =
      if layer = 0
      then ()
      else begin
        let layer' : nat = layer - 1 in
        if layer' >= Seq.length pl
        then failwith "IMPOSSIBLE: index out of bounds in print_witness_as_c_aux";
        let (buf, off) = Seq.index pl layer' in
        out (Printf.sprintf
"{   uint8_t *tmpptr = witness%s%d[%d].buf; memcpy(&witness%s%d[%d].buf[%d], (uint8_t* ) (void* ) &tmpptr, sizeof(uint8_t* )); }"
          flight
          num
          layer
          flight
          num
          buf
          off
       )
      end
    in
    if len = 0
    then ()
    else aux2 (len - 1)

let print_witness_as_c_gen
  (out: (string -> ML unit))
  (print_c_initializer: bool)
  (flight: string)
  (witness: Seq.seq (Seq.seq int))
  (pointer_locs: option (Seq.seq (int & int)))
  (f: (len: int { len == Seq.length witness }) -> ML unit)
  (num: nat)
: ML unit
= let len = Seq.length witness in
  out "{\n";
  print_witness_as_c_aux out true flight witness pointer_locs len num;
  out "
  printf(\"";
  print_witness_as_c_aux out print_c_initializer flight witness pointer_locs len num;
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
  (i: nat)
  (out_dir: string)
  (validator_name: string)
  (args: list string)
: ML string
= OS.concat out_dir (mk_args_as_file_name ("witness." ^ string_of_int i ^ "." ^ validator_name) args ^ ".dat")

let write_witness_to_file
  (witness: Seq.seq (Seq.seq int))
  (mk_output_filename: (int -> ML string))
: ML unit
= let rec aux (i: nat) : ML unit =
    if i >= Seq.length witness
    then ()
    else begin
      let witness = Seq.index witness i in
      OS.write_witness_to_file (Seq.seq_to_list witness) (mk_output_filename i);
      aux (i + 1)
    end
  in
  aux 0

let incr (x: ref nat) : ML nat =
  let res = !x in
  x := res + 1;
  res

let print_witness_as_c
  (out_dir: string)
  (out: (string -> ML unit))
  (print_c_initializer: bool)
  (p: prog)
  (positive: bool)
  (flight: string)
  (validator_name: string)
  (arg_types: list (string & arg_type))
  (counter: ref nat)
  (witness: Seq.seq (Seq.seq int))
  (pointer_locs: option (Seq.seq (int & int)))
  (args: list string)
: ML unit
= let num = incr counter in
  write_witness_to_file witness (fun i -> mk_output_filename num out_dir ((if positive then "POS." else "NEG.") ^ string_of_int i ^ "." ^ validator_name) args);
  print_witness_as_c_gen out print_c_initializer flight witness pointer_locs (fun len ->
    if len = 0
    then failwith "print_witness_as_c: no witness layers. This should not happen.";
    print_witness_call_as_c (Some? pointer_locs) out p positive flight validator_name arg_types args num len
  ) num

let print_diff_witness_as_c
  (out_dir: string)
  (out: (string -> ML unit))
  (print_c_initializer: bool)
  (p: prog)
  (flight: string)
  (validator_name1: string)
  (validator_name2: string)
  (arg_types: list (string & arg_type))
  (counter: ref nat)
  (witness: Seq.seq (Seq.seq int))
  (pointer_locs: option (Seq.seq (int & int)))
  (args: list string)
: ML unit
= let num = incr counter in
  write_witness_to_file witness (fun i -> mk_output_filename num out_dir ("POS." ^ string_of_int i ^ "." ^ validator_name1 ^ ".NEG." ^ validator_name2) args);
  print_witness_as_c_gen out print_c_initializer flight witness pointer_locs (fun len ->
    if len = 0
    then failwith "print_witness_as_c: no witness layers. This should not happen.";
    print_witness_call_as_c (Some? pointer_locs) out p true flight validator_name1 arg_types args num len;
    print_witness_call_as_c (Some? pointer_locs) out p false flight validator_name2 arg_types args num len
  )
  num

let print_witness (witness: Seq.seq (Seq.seq int)) : ML unit =
  FStar.IO.print_string " produced witness: [";
  let p witness = List.iter (fun i -> FStar.IO.print_string (string_of_int i); FStar.IO.print_string "; ") (Seq.seq_to_list witness) in
  List.iter (fun i -> FStar.IO.print_string "["; p i; FStar.IO.print_string "] ") (Seq.seq_to_list witness);
  FStar.IO.print_string "]"

let print_branch_trace (witness: Seq.seq int) : ML unit =
  FStar.IO.print_string " with branch trace : [";
  List.iter (fun i -> FStar.IO.print_string (string_of_int i); FStar.IO.print_string "; ") (Seq.seq_to_list witness);
  FStar.IO.print_string "]"

let rec mk_witness_call (accu: string) (l: list arg_type) (args: list string) : Tot string (decreases l) =
  match l, args with
  | ArgCopyBuffer :: q, _
  | ArgPointer _ :: q, _ -> mk_witness_call (Printf.sprintf "%s 0" accu) q args
  | ArgSimple _ :: ql, a :: qargs -> mk_witness_call (Printf.sprintf "%s %s" accu a) ql qargs
  | ArgSimple _ :: _, []
  | [], _
    -> Printf.sprintf "(%s)" accu

let print_witness_and_call (name: string) (l: list arg_type) (witness: Seq.seq (Seq.seq int)) (input_size: string) (branch_trace: Seq.seq int) (args: list string) : ML unit =
  FStar.IO.print_string ";; call ";
  FStar.IO.print_string (mk_witness_call name l args);
  print_witness witness;
  FStar.IO.print_string (Printf.sprintf " with remaining input %s " input_size);
  print_branch_trace branch_trace;
  FStar.IO.print_string "\n"

let count_args (l: list arg_type) : Tot nat = List.Tot.length (List.Tot.filter (function ArgCopyBuffer | ArgPointer _ -> false | ArgSimple _ -> true) l)

let rec mk_choose_conj_layer (array_index: string) (witness: Seq.seq int) (accu: string) (i: nat) : Tot string
  (decreases (if i >= Seq.length witness then 0 else Seq.length witness - i))
= if i >= Seq.length witness
  then accu
  else mk_choose_conj_layer array_index witness ("(and (= "^choose array_index (string_of_int i) ^ " " ^ string_of_int (Seq.index witness i)^") "^accu^")") (i + 1)

let rec mk_choose_conj (witness: Seq.seq (Seq.seq int)) (accu: string) (i: nat) : Tot string
  (decreases (if i >= Seq.length witness then 0 else Seq.length witness - i))
= if i >= Seq.length witness
  then accu
  else
    let w = Seq.index witness i in
    let accu1 = mk_choose_conj_layer (string_of_int i) w accu 0 in
    let accu2 = Printf.sprintf "(and (= (state-witness-size %d) %d) %s)" i (Seq.length w) accu1 in
    mk_choose_conj witness accu2 (i + 1)

let rec mk_arg_conj (accu: string) (i: nat) (l: list string) : Tot string (decreases l) =
  match l with
  | [] -> accu
  | arg :: q ->
    mk_arg_conj (Printf.sprintf "(and %s (= arg-%d %s))" accu i arg) (i + 1) q

let mk_want_another_distinct_witness witness witness_args : Tot string =
  Printf.sprintf
"(assert (not %s))
"
  (mk_arg_conj (mk_choose_conj witness ("(= (next-array-index state-witness) "^string_of_int (Seq.length witness)^")") 0) 0 witness_args)

let rec want_witnesses (use_ptr: bool) (print_test_case: (Seq.seq (Seq.seq int) -> option (Seq.seq (int & int)) -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) i : ML unit =
  z3.to_z3 "(check-sat)\n";
  let status = z3.from_z3 () in
  if status = "sat" then begin
    z3.to_z3 "(eval (input-size state-witness))\n";
    let input_size = z3.from_z3 () in
    let (witness, pointer_locs) = read_witness use_ptr z3 in
    let witness_args = read_witness_args z3 [] nargs in
    let branch_trace = read_branch_trace z3 in
    print_witness_and_call name l witness input_size branch_trace witness_args;
    print_test_case witness pointer_locs witness_args;
    z3.to_z3 (mk_want_another_distinct_witness witness witness_args);
    if i <= 1
    then ()
    else
      want_witnesses use_ptr print_test_case z3 name l nargs (i - 1)
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

let rec mk_call_args (accu: string) (i: nat) (l: list arg_type) : Tot string (decreases l) =
  match l with
  | [] -> accu
  | ArgCopyBuffer :: q
  | ArgPointer _ :: q -> mk_call_args (Printf.sprintf "%s 0" accu) i q
  | ArgSimple _ :: q -> mk_call_args (Printf.sprintf "%s arg-%d" accu i) (i + 1) q

let rec mk_assert_args (accu: string) (i: nat) (l: list arg_type) : Tot string (decreases l) =
  match l with
  | [] -> accu
  | ArgCopyBuffer :: q
  | ArgPointer _ :: q -> mk_assert_args accu i q
  | ArgSimple ArgBool :: q -> mk_assert_args (Printf.sprintf "%s(declare-fun arg-%d () Bool)\n" accu i) (i + 1) q
  | ArgSimple (ArgInt it) :: q -> mk_assert_args (Printf.sprintf "%s(declare-fun arg-%d () Int)\n(assert (and (<= 0 arg-%d) (< arg-%d %d)))\n" accu i i i (pow2 (integer_type_bit_size it))) (i + 1) q

let mk_get_witness (name: string) (l: list arg_type) : string =
Printf.sprintf "
%s
(define-fun state-witness () State (%s initial-state))
(define-fun state-witness-input-size () Int (input-size state-witness))
(assert (<= (state-witness-size 0) (choice-index state-witness)))
(assert (>= (state-witness-size 0) (choice-index state-witness)))
"
  (mk_assert_args "" 0 l)
  (mk_call_args name 0 l)

noeq
type branch_trace_node =
| Node: value: nat -> children: list branch_trace_node -> branch_trace_node

let assert_valid_state =
  "(assert (or (= state-witness-input-size -1) (= state-witness-input-size 0)))\n"

let rec enumerate_branch_traces'
  (z3: Z3.z3)
  (max_depth cur_depth: nat)
  (branch_trace: string)
: ML (list branch_trace_node)
= if max_depth = cur_depth
  then []
  else begin
    z3.to_z3 (Printf.sprintf "(assert (> (branch-index state-witness) %d))\n" cur_depth);
    z3.to_z3 "(check-sat)\n";
    let status = z3.from_z3 () in
    if status = "sat"
    then
      let rec aux accu choice : ML (list branch_trace_node) =
        let branch_trace' = branch_trace ^ " " ^ string_of_int choice in
        FStar.IO.print_string (Printf.sprintf "Checking feasibility of branch trace: %s\n" branch_trace');
        z3.to_z3 "(push)\n";
        z3.to_z3 (Printf.sprintf "(assert (= (branch-trace %d) %d))\n" cur_depth choice);
        z3.to_z3 "(check-sat)\n";
        let status = z3.from_z3 () in
        if status = "unsat"
        then begin
          FStar.IO.print_string "Branch condition is always false\n";
          z3.to_z3 "(pop)\n";
          aux accu (choice + 1)
        end
        else if status = "sat"
        then begin
          FStar.IO.print_string "Branch condition may hold. Checking validity for parser encoding\n";
          z3.to_z3 "(push)\n";
          z3.to_z3 assert_valid_state;
          z3.to_z3 "(check-sat)\n";
          let status = z3.from_z3 () in
          z3.to_z3 "(pop)\n";
          if status = "sat"
          then begin
            FStar.IO.print_string "Branch is valid\n";
            let res = enumerate_branch_traces' z3 max_depth (cur_depth + 1) branch_trace' in
            z3.to_z3 "(pop)\n";
            aux (Node choice res :: accu) (choice + 1)
          end
          else begin
            FStar.IO.print_string "Branch is invalid or Z3 gave up\n";
            z3.to_z3 "(pop)\n";
            List.Tot.rev accu
          end
        end
        else begin
          FStar.IO.print_string "Z3 gave up evaluating branch condition. Aborting\n";
          z3.to_z3 "(pop)\n";
          List.Tot.rev accu
        end
      in
      aux [] 0
    else begin
      FStar.IO.print_string "Cannot take further branches under this case\n";
      []
    end
  end

let enumerate_branch_traces
  (z3: Z3.z3)
  (max_depth: nat)
: ML (list branch_trace_node)
= z3.to_z3 "(push)\n";
  let res = enumerate_branch_traces' z3 max_depth 0 "" in
  z3.to_z3 "(pop)\n";
  res

let rec want_witnesses_with_depth
  (use_ptr: bool)
  (print_test_case: (Seq.seq (Seq.seq int) -> option (Seq.seq (int & int)) -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) nbwitnesses
  cur_depth (tree: list branch_trace_node) (branch_trace: string)
: ML unit
=
  FStar.IO.print_string (Printf.sprintf "Checking witnesses for branch trace: %s\n" branch_trace);
  want_witnesses use_ptr print_test_case z3 name l nargs nbwitnesses;
  z3.to_z3 (Printf.sprintf "(assert (> (branch-index state-witness) %d))\n" cur_depth);
  let rec aux (tree: list branch_trace_node) : ML unit = match tree with
  | [] -> ()
  | Node choice tree' :: q ->
    z3.to_z3 "(push)\n";
    z3.to_z3 (Printf.sprintf "(assert (= (branch-trace %d) %d))\n" cur_depth choice);
    want_witnesses_with_depth use_ptr print_test_case z3 name l nargs nbwitnesses (cur_depth + 1) tree' (branch_trace ^ " " ^ string_of_int choice);
    z3.to_z3 "(pop)\n";
    aux q
  in
  aux tree

let witnesses_for (use_ptr: bool) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) (print_test_case_mk_get_first_witness: list ((Seq.seq (Seq.seq int) -> option (Seq.seq (int & int)) -> list string -> ML unit) & (unit -> ML string))) nbwitnesses max_depth =
  z3.to_z3 "(push)\n";
  z3.to_z3 (mk_get_witness name l);
  let traces = enumerate_branch_traces z3 max_depth in
  z3.to_z3 assert_valid_state;
  List.iter
    #((Seq.seq (Seq.seq int) -> option (Seq.seq (int & int)) -> list string -> ML unit) & (unit -> ML string))
    (fun (ptc, f) ->
      z3.to_z3 "(push)\n";
      z3.to_z3 (f ());
      want_witnesses_with_depth use_ptr ptc z3 name l nargs nbwitnesses 0 traces "";
      z3.to_z3 "(pop)\n"
    )
    print_test_case_mk_get_first_witness
    ;
  z3.to_z3 "(pop)\n"

let mk_get_positive_test_witness (name: string) (l: list arg_type) : string =
"
(assert (= (input-size state-witness) 0)) ; validator shall consume all input
"

let mk_get_negative_test_witness (name: string) (l: list arg_type) : string =
"
(assert (= state-witness-input-size -1)) ; validator shall genuinely fail, we are not interested in positive cases followed by garbage
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
    printf(\"// Reached from position %\" PRIu64 \": type name %s, field name %s\\n\", start_pos, typename_s, fieldname);
  } else {
    printf(\"// Parsing failed at position %\" PRIu64 \": type name %s, field name %s. Reason: %s\\n\", start_pos, typename_s, fieldname, reason);
    *context = 1;
  }
}

typedef struct {
  uint8_t *buf;
  uint64_t len;
} witness_layer_t;
"

let test_default_probe_functions = "
typedef struct {
  witness_layer_t *layers;
  uint64_t count;
  uint64_t cur;
} copy_buffer_t;

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
  copy_buffer_t *state = ((copy_buffer_t * ) x);
  return state->layers[state->cur].buf;
}

uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
  copy_buffer_t *state = ((copy_buffer_t * ) x);
  return state->layers[state->cur].len;
}
"

let test_ptr_probe_functions = "
typedef witness_layer_t copy_buffer_t;

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
  copy_buffer_t *state = ((copy_buffer_t * ) x);
  return state->buf;
}

uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
  copy_buffer_t *state = ((copy_buffer_t * ) x);
  return state->len;
}
"

let test_probe_functions (use_ptr: bool) : Tot string =
  if use_ptr then test_ptr_probe_functions else test_default_probe_functions

let generate_default_probe_function (name: string) : Tot string = "
BOOLEAN "^name^"(uint64_t len, uint64_t ro, uint64_t wo, uint64_t src, EVERPARSE_COPY_BUFFER_T dst) {
  if (ro != 0 || wo != 0) {
    printf(\"ProbeAndCopy: ro and wo must be 0\\n\");
    exit(4);
  };
  copy_buffer_t *state = (copy_buffer_t * ) dst;
  if (src < state->count) {
    uint64_t got_len = state->layers[src].len;
    if (len != got_len) {
      printf(\"ProbeAndCopy: layer length does not match spec. Expected %\" PRIu64 \", got %\" PRIu64 \"\\n\", len, got_len);
      exit(4);
    } else {
      state->cur = src;
      return true;
    }
  } else {
    printf(\"ProbeAndCopy: incorrect pointer\\n\");
    exit(4);
  }
}
"

let generate_ptr_probe_function (name: string) : Tot string = "
BOOLEAN "^name^"(uint64_t len, uint64_t ro, uint64_t wo, uint64_t src, EVERPARSE_COPY_BUFFER_T dst) {
  if (ro != 0 || wo != 0) {
    printf(\"ProbeAndCopy: ro and wo must be 0\\n\");
    exit(4);
  };
  copy_buffer_t *state = (copy_buffer_t * ) dst;
  state->buf = (uint8_t* ) (void* ) src;
  state->len = len;
  return true;
}
"

let generate_probe_init_function (name: string) : Tot string = "
BOOLEAN "^name^"(uint64_t src, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  (void)(src);
  (void)(len);
  (void)(dst);
  return true;
}
"

let generate_probe_function (use_ptr: bool) (name: string) : Tot string =
  if use_ptr
  then generate_ptr_probe_function name
  else generate_default_probe_function name

let cout_test_probe_functions
  (use_ptr: bool)
  (cout: string -> ML unit)
  (prog: prog)
: ML unit
= cout (test_probe_functions use_ptr);
  List.iter
    (fun x -> match x with
    | (name, ProgProbe T.PQWithOffsets) ->
      cout (generate_probe_function use_ptr name)
    | (name, ProgProbe T.PQInit) ->
      cout (generate_probe_init_function name)
    | _ -> ()
    )
    prog

let do_test (out_dir: string) (out_file: option string) (z3: Z3.z3)
  (use_ptr: bool)
  (print_c_initializer: bool)
  (flight: string) (prog: prog) (name1: string) (nbwitnesses: int) (depth: nat) (pos: bool) (neg: bool) : ML unit =
  let def = List.assoc name1 prog in
  begin match def with
  | Some (ProgDef _ _) -> ()
  | _ -> failwith (Printf.sprintf "do_test: parser %s not found" name1)
  end;
  let Some (ProgDef args _) = def in
  let sargs = List.Tot.map snd args in
  let modul, validator_name = module_and_validator_name name1 in
  let nargs = count_args sargs in with_option_out_file out_file (fun cout ->
  cout "#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include \"";
  cout modul;
  cout ".h\"
";
  cout test_error_handler;
  cout_test_probe_functions use_ptr cout prog;
  cout "
  int main(void) {
";
  let counter = alloc 0 in
  let tasks =
    begin
      if pos
      then [print_witness_as_c out_dir cout print_c_initializer prog true flight validator_name args counter, (fun _ -> (
        FStar.IO.print_string (Printf.sprintf ";; Positive test witnesses for %s\n" name1);
        mk_get_positive_test_witness name1 sargs
      ))]
      else []
    end `List.Tot.append`
    begin
      if neg
      then [print_witness_as_c out_dir cout print_c_initializer prog false flight validator_name args counter, (fun _ -> (
        FStar.IO.print_string (Printf.sprintf ";; Negative test witnesses for %s\n" name1);
        mk_get_negative_test_witness name1 sargs
      ))]
      else []
    end
  in
  witnesses_for use_ptr z3 name1 sargs nargs tasks nbwitnesses depth;
  cout "  return 0;
  }
"
  )

let mk_get_diff_test_witness (name1: string) (l: list arg_type) (name2: string) : string =
  let call2 = mk_call_args name2 0 l in
  Printf.sprintf
"
%s
(define-fun negative-state-witness () State (%s %s)) ; branch trace is ignored for the second parser
(assert (not (= (input-size negative-state-witness) 0))) ; test cases that do not consume everything are considered failing
(assert (>= (input-size negative-state-witness) -1)) ; do not record tests that artificially fail due to SMT2 encoding
"
  (mk_get_positive_test_witness name1 l)
  call2
  (mk_state "(state-witness-size 0)" "0" "0" "1" "-1")

let do_diff_test_for
  (out_dir: string) (counter: ref nat) (cout: string -> ML unit) (z3: Z3.z3)
  (use_ptr: bool)
  (print_c_initializer: bool)
  (flight: string) (prog: prog) name1 name2 (args: list (string & arg_type)) (nargs: nat { nargs == count_args (List.Tot.map snd args) }) validator_name1 validator_name2 nbwitnesses depth =
  FStar.IO.print_string (Printf.sprintf ";; Witnesses that work with %s but not with %s\n" name1 name2);
  let sargs = List.Tot.map snd args in
  witnesses_for use_ptr z3 name1 sargs nargs ([print_diff_witness_as_c out_dir cout print_c_initializer prog flight validator_name1 validator_name2 args counter, (fun _ -> mk_get_diff_test_witness name1 sargs name2)]) nbwitnesses depth

let do_diff_test (out_dir: string) (out_file: option string) (z3: Z3.z3)
  (use_ptr: bool)
  (print_c_initializer: bool)
  (flight: string) (prog: prog) name1 name2 nbwitnesses depth =
  let def = List.assoc name1 prog in
  begin match def with
  | Some (ProgDef _ _) -> ()
  | _ -> failwith (Printf.sprintf "do_test: parser %s not found" name1)
  end;
  let Some (ProgDef args _) = def in
  let sargs = List.Tot.map snd args in
  let def2 = List.assoc name2 prog in
  if None? def2
  then failwith (Printf.sprintf "do_diff_test: parser %s not found" name2);
  if def2 <> def
  then failwith (Printf.sprintf "do_diff_test: parsers %s and %s do not have the same arg types" name1 name2);
  let nargs = count_args sargs in
  let modul1, validator_name1 = module_and_validator_name name1 in
  let modul2, validator_name2 = module_and_validator_name name2 in
  with_option_out_file out_file (fun cout ->
  cout "#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <stdio.h>
#include <stdbool.h>
#include \"";
  cout modul1;
  cout ".h\"
#include \"";
  cout modul2;
  cout ".h\"
";
  cout test_error_handler;
  cout_test_probe_functions use_ptr cout prog;
  cout "
  int main(void) {
";
  let counter = alloc 0 in
  do_diff_test_for out_dir counter cout z3 print_c_initializer use_ptr flight prog name1 name2 args nargs validator_name1 validator_name2 nbwitnesses depth;
  do_diff_test_for out_dir counter cout z3 print_c_initializer use_ptr flight prog name2 name1 args nargs validator_name2 validator_name1 nbwitnesses depth;
  cout "  return 0;
  }
"
)

let test_exe_mk_arg
  (accu: (int & string & string & string))
  (pn: (string & arg_type))
: Tot (int & string & string & string)
=
  let (arg_var, p) = pn in
  let (cur_arg, read_args, call_args_lhs, call_args_rhs) = accu in
  let cur_arg_s = string_of_int cur_arg in
  let cur_arg' = cur_arg + begin match p with
  | ArgCopyBuffer
  | ArgPointer _ -> 0
  | ArgSimple _ -> 1
  end
  in
  let read_args' = read_args ^
  begin match p with
  | ArgSimple (ArgInt _) -> "
  unsigned long long "^arg_var^" = strtoull(argv["^cur_arg_s^"], NULL, 0);
"
  | ArgSimple ArgBool -> "
  BOOLEAN "^arg_var^" = (strcmp(argv["^cur_arg_s^"], \"true\") == 0);
  if (! ("^arg_var^" || strcmp(argv["^cur_arg_s^"], \"false\") == 0)) {
    printf(\"Argument %d must be true or false, got %s\\n\", "^cur_arg_s^", argv["^cur_arg_s^"]);
    return 1;
  }
"
  | ArgCopyBuffer -> "" // FIXME: support probe in generic test executable
  | ArgPointer pt -> alloc_ptr_arg arg_var pt
  end
  in
  let call_args_lhs' = call_args_lhs ^ arg_var ^ ", " in
  let call_args_rhs' = call_args_lhs ^ ", " ^ arg_var in
  (cur_arg', read_args', call_args_lhs', call_args_rhs')

let test_checker_c
  (modul: string)
  (validator_name: string)
  (outparameters: string)
  (params: list (string & arg_type))
: Tot string
=
  let (nb_cmd_and_args, read_args, call_args_lhs, call_args_rhs) = List.Tot.fold_left test_exe_mk_arg (2, "", "", "") params in
  let nb_cmd_and_args_s = string_of_int nb_cmd_and_args in
  let nb_args_s = string_of_int (nb_cmd_and_args - 1) in
  "
#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include \""^modul^".h\"
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <stdint.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

"^test_error_handler^"

int main(int argc, char** argv) {
  if (argc < "^nb_cmd_and_args_s^") {
    printf(\"Wrong number of arguments, expected "^nb_args_s^", got %d\\n\", argc - 1);
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
    close(testfile);
    printf(\"File is too large. EverParse/3D only supports data up to 4 GB\");
    return 3;
  }
  uint8_t dummy = 42;
  uint8_t * buf = &dummy; // for zero-sized files (mmap does not support zero-sized mappings)
  void * vbuf = NULL;
  if (len > 0) {
    vbuf = mmap(NULL, len, PROT_READ, MAP_PRIVATE, testfile, 0);
    if (vbuf == MAP_FAILED) {
      close(testfile);
      printf(\"Cannot read %\" PRIuPTR \" bytes from %s\\n\", len, filename);
      return 3;
    };
    buf = (uint8_t *) vbuf;
  };
  printf(\"Read %\" PRIuPTR \" bytes from %s\\n\", len, filename);
  uint8_t context = 0;
  uint64_t result = "^validator_name^"("^call_args_lhs^"&context, &TestErrorHandler, buf, len, 0);
  if (len > 0)
    munmap(vbuf, len);
  close(testfile);
  if (EverParseIsError(result)) {
    printf(\"// Witness from %s REJECTED because validator failed\\n\", filename);
    return 2;
  };
  if (result != (uint64_t) len) { // consistent with the postcondition of validate_with_action_t' (see also valid_length)
    printf(\"// Witness from %s REJECTED because validator only consumed %\" PRIu64 \" out of %\" PRIuPTR \" bytes\\n\", filename, result, len);
    return 1;
  }
  printf(\"// Witness from %s ACCEPTED\\n\", filename);
  "^outparameters^"
  return 0;
}
"

let produce_test_checker_exe (out_file: string) (prog: prog) (name1: string) : ML unit =
  let def = List.assoc name1 prog in
  begin match def with
  | Some (ProgDef _ _) -> ()
  | _ -> failwith (Printf.sprintf "do_test: parser %s not found" name1)
  end;
  let Some (ProgDef args _) = def in
  let modul, validator_name = module_and_validator_name name1 in
  let outparameters : ref string = alloc "" in
  let outp s : ML unit = outparameters := !outparameters ^ s in
  print_outparameters outp prog args;
  with_out_file out_file (fun cout ->
    cout (test_checker_c modul validator_name !outparameters args)
  )
