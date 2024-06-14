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
(declare-datatypes () ((State (mk-state (input-size Int) (choice-index Int) (branch-index Int)))))
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

(declare-fun choose (Int) Int)
(assert (forall ((i Int))
  (and (<= 0 (choose i)) (< (choose i) 256))
))

(declare-fun branch-trace (Int) Int)

(define-fun parse-false ((x State)) State
  (mk-state -1 (choice-index x) (branch-index x))
)

(define-fun parse-all-bytes ((x State)) State
  (if (<= (input-size x) 0)
    x
    (mk-state 0 (+ (choice-index x) (input-size x)) (branch-index x))
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
      (branch-index x)
    )
  )
)

(define-fun parse-u8 ((x State)) Result
  (mk-result
    (choose (choice-index x))
    (mk-state
      (let ((new-size (- (input-size x) 1)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 1)
      (branch-index x)
    )
  )
)

(define-fun parse-u16-be ((x State)) Result
  (mk-result
    (+ (choose (+ 1 (choice-index x)))
      (* 256
        (choose (+ 0 (choice-index x)))
      )
    )
    (mk-state
      (let ((new-size (- (input-size x) 2)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 2)
      (branch-index x)
    )
  )
)

(define-fun parse-u16-le ((x State)) Result
  (mk-result
    (+ (choose (+ 0 (choice-index x)))
      (* 256
        (choose (+ 1 (choice-index x)))
      )
    )
    (mk-state
      (let ((new-size (- (input-size x) 2)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 2)
      (branch-index x)
    )
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
    (mk-state
      (let ((new-size (- (input-size x) 4)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 4)
      (branch-index x)
    )
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
    (mk-state
      (let ((new-size (- (input-size x) 4)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 4)
      (branch-index x)
    )
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
    (mk-state
      (let ((new-size (- (input-size x) 8)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 8)
      (branch-index x)
    )
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
    (mk-state
      (let ((new-size (- (input-size x) 8)))
        (if (< new-size 0)
          -1
          new-size
        )
      )
      (+ (choice-index x) 8)
      (branch-index x)
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
      (mk-state
        (- (input-size x) size)
        (+ (choice-index x) size)
        (branch-index x)
      )
      (mk-state
        -1
        (choice-index x)
        (branch-index x)
      )
    )
  )
)

(declare-const initial-input-size Int)
(assert (>= initial-input-size 0))
(define-fun initial-state () State (mk-state initial-input-size 0 0))

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
  | I.DT_App _ hd args -> parse_readable_app hd args

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
  let condtmp = Printf.sprintf "%s-condtmp" name in
"(define-fun "^name^" ("^binders^"("^input^" State)) State
   (let (("^tmp^" ("^dfst^" "^input^")))
     (if (< (input-size (after-state "^tmp^")) 0)
       (after-state "^tmp^")
       (let (("^condtmp^" (let (("^cond_binder_name^" (return-value "^tmp^"))) "^cond^")))
         (if (and "^condtmp^" (or (< (branch-index (after-state "^tmp^")) 0) (= (branch-trace (branch-index (after-state "^tmp^"))) 0)))
           (let (("^dsnd_binder_name^" (return-value "^tmp^")))
             ("^dsnd^"
               (mk-state
                 (input-size (after-state "^tmp^"))
                 (choice-index (after-state "^tmp^"))
                 (+ (if (< (branch-index (after-state "^tmp^")) 0) 0 1) (branch-index (after-state "^tmp^")))
               )
             )
           )
           (mk-state
             (if (and (not "^condtmp^") (or (< (branch-index (after-state "^tmp^")) 0) (= (branch-trace (branch-index (after-state "^tmp^"))) 1))) -1 -2)
             (choice-index (after-state "^tmp^"))
             (+ (if (< (branch-index (after-state "^tmp^")) 0) 0 1) (branch-index (after-state "^tmp^")))
           )
         )
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
     ("^f_then^" (if (< (branch-index "^input^") 0) "^input^" (mk-state (input-size "^input^") (choice-index "^input^") (+ 1 (branch-index "^input^")))))
     (if (not "^cond^")
       ("^f_else^" "^input^")
       (mk-state -2 (choice-index "^input^") (+ (if (< (branch-index "^input^") 0) 0 1) (branch-index "^input^"))) ; this is a Z3 encoding artifact, not a parsing failure
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
   (let (("^tmp^" (if (< (branch-index "^input^") 0) "^input^" (mk-state (input-size "^input^") (choice-index "^input^") (+ 1 (branch-index "^input^"))))))
     (if (and "^cond^" (or (< (branch-index "^input^") 0) (= (branch-trace (branch-index "^input^")) "^string_of_int counter^")))
       ("^f_then^" "^tmp^")
       (if (and (not "^cond^") (or (< (branch-index "^input^") 0) (= (branch-trace (branch-index "^input^")) "^string_of_int (1 + counter)^")))
         ("^f_else^" "^tmp^")
         (mk-state -2 (choice-index "^tmp^") (+ (if (< (branch-index "^input^") 0) 0 1) (branch-index "^input^"))) ; this is a Z3 encoding artifact, not a parsing failure
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
      (mk-state -1 (choice-index "^input^") (branch-index "^input^"))
      (let (("^res^" ("^body^" (mk-state "^sz^" (choice-index "^input^") (branch-index "^input^")))))
        (mk-state
          (if (= (input-size "^res^") 0)
            (- (input-size "^input^") "^sz^")
            (if (> (input-size "^res^") 0)
              -1
              (input-size "^res^")
            )
          )
          (choice-index "^res^")
          (branch-index "^res^")
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
      (mk-state -1 (choice-index (after-state "^tmp^")) (branch-index (after-state "^tmp^")))
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
  | I.T_probe_then_validate _ _ _ _ _
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

let rec typ_depth (t: I.typ) : GTot nat
  (decreases t)
= match t with
  | I.T_if_else _ t1 t2 // 2 accounts for the call to parse_then_else_with_branch_trace
    -> 2 + typ_depth t1 + typ_depth t2
  | I.T_pair _ t1 t2
    -> 1 + typ_depth t1 + typ_depth t2
  | I.T_dep_pair _ _ (_, t')
  | I.T_dep_pair_with_refinement _ _ _ (_, t')
  | I.T_with_comment _ t' _
  | I.T_at_most _ _ t'
  | I.T_exact _ _ t'
  | I.T_nlist _ _ t'
    -> 1 + typ_depth t'
  | _
    -> 0

let rec parse_typ (t : I.typ) : Pure (parser not_reading)
  (requires (type_has_actions t == false))
  (ensures (fun _ -> True))
  (decreases (typ_depth t))
= 
  match t with
  | I.T_false _ -> parse_false
  | I.T_denoted _ d -> parse_denoted d
  | I.T_pair _ t1 t2 -> parse_pair (parse_typ t1) (parse_typ t2)
  | I.T_dep_pair _ t1 (lam, t2) -> parse_dep_pair (parse_readable_dtyp t1) lam (parse_typ t2)
  | I.T_refine _ base (lam, cond) -> parse_refine (parse_readable_dtyp base) lam (fun _ -> mk_expr cond)
  | I.T_dep_pair_with_refinement _ base (lam_cond, cond) (lam_k, k) -> parse_dep_pair_with_refinement (parse_readable_dtyp base) lam_cond (fun _ -> mk_expr cond) lam_k (parse_typ k)
  | I.T_if_else cond t1 t2 -> parse_ifthenelse cond t1 t2 0
  | I.T_with_comment _ base _ -> parse_typ base
  | I.T_at_most _ size body -> parse_at_most (fun _ -> mk_expr size) (parse_typ body)
  | I.T_exact _ size body -> parse_exact (fun _ -> mk_expr size) (parse_typ body)
  | I.T_string _ elt terminator -> parse_string (parse_readable_dtyp elt) (fun _ -> mk_expr terminator)
  | I.T_nlist _ size body ->
    if match body with
    | I.T_denoted _ (I.DT_IType i) -> Some? (itype_byte_size i)
    | _ -> false
    then
      let I.T_denoted _ (I.DT_IType i) = body in
      parse_nlist_total_constant_size i size
    else
      parse_nlist (fun _ -> mk_expr size) (parse_typ body)

and parse_ifthenelse (cond: I.expr) (tthen: I.typ) (telse: I.typ) : Pure (int -> parser not_reading)
  (requires (type_has_actions tthen == false /\ type_has_actions telse == false))
  (ensures (fun _ -> True))
  (decreases (1 + typ_depth tthen + typ_depth telse))
= match telse with
  | I.T_if_else cond2 tthen2 telse2 ->
    parse_ifthenelse_cons (fun _ -> mk_expr cond) (parse_typ tthen) (parse_ifthenelse cond2 tthen2 telse2)
  | _ ->
    parse_ifthenelse_nil (fun _ -> mk_expr cond) (parse_typ tthen) (parse_typ telse)

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
  | T.Extern_probe _
  -> ()

type prog_def = {
  args: list arg_type;
  enum_base_type: option arg_type;
}

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
      | Some def -> def.enum_base_type
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
  if type_has_actions a.typ then failwith (Printf.sprintf "produce_type_decl: %s still has some actions" name);
  let _ = parse_typ a.typ name binders true out in
  (name, {
    args = List.map (fun (i, ty) -> match arg_type_of_typ_with_prog accu ty with Some t -> t | None -> failwith (Printf.sprintf "Parser %s has unsupported argument type for %s" name (ident_to_string i))) a.name.td_params;
    enum_base_type = begin match a.enum_typ with
    | Some ty -> arg_type_of_typ_with_prog accu ty
    | _ -> None
    end;
  }) :: accu

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
  (out_dir: string)
  (validator_name: string)
  (args: list string)
: ML string
= let i = !counter in
  counter := i + 1;
  OS.concat out_dir (mk_args_as_file_name ("witness." ^ string_of_int i ^ "." ^ validator_name) args ^ ".dat")

let print_witness_as_c
  (out_dir: string)
  (out: (string -> ML unit))
  (positive: bool)
  (validator_name: string)
  (arg_types: list arg_type)
  (counter: ref int)
  (witness: Seq.seq int)
  (args: list string)
: ML unit
= OS.write_witness_to_file (Seq.seq_to_list witness) (mk_output_filename counter out_dir ((if positive then "POS." else "NEG.") ^ validator_name) args);
  print_witness_as_c_gen out witness (fun len ->
    print_witness_call_as_c out positive validator_name arg_types len args
  )

let print_diff_witness_as_c
  (out_dir: string)
  (out: (string -> ML unit))
  (validator_name1: string)
  (validator_name2: string)
  (arg_types: list arg_type)
  (counter: ref int)
  (witness: Seq.seq int)
  (args: list string)
: ML unit
= OS.write_witness_to_file (Seq.seq_to_list witness) (mk_output_filename counter out_dir ("POS." ^ validator_name1 ^ ".NEG." ^ validator_name2) args);
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

let check_timeout_exceeded (timeout: option nat) : ML bool =
  match timeout with
  | None -> false
  | Some timeout ->
    let res = OS.timestamp () > timeout in
    if res then FStar.IO.print_string "3D global timeout exceeded!\n";
    res

let send_check_sat (z3: Z3.z3) (timeout: option nat) : ML unit =
  begin match timeout with
  | None -> ()
  | Some timeout ->
    let timeout = timeout - OS.timestamp () in
    let timeout : nat = if timeout > 0 then timeout * 1000 else 1 in // z3 expects milliseconds, we have seconds
    let timeout_cmd = Printf.sprintf "(set-option :timeout %d)\n" timeout in
    FStar.IO.print_string timeout_cmd;
    z3.to_z3 timeout_cmd
  end;
  z3.to_z3 "(check-sat)\n"

let rec want_witnesses (timeout: option nat) (print_test_case: (Seq.seq int -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) i (accu_no_dup: string) : ML string =
  send_check_sat z3 timeout;
  let status = z3.from_z3 () in
  if status = "sat" then begin
    let witness = read_witness z3 in
    let witness_args = read_witness_args z3 [] nargs in
    print_witness_and_call name l witness witness_args;
    print_test_case witness witness_args;
    let new_no_dup = mk_want_another_distinct_witness witness witness_args in
    let accu_no_dup' = accu_no_dup ^ new_no_dup in
    z3.to_z3 new_no_dup;
    if
      if check_timeout_exceeded timeout
      then true
      else i <= 1
    then accu_no_dup'
    else
      want_witnesses timeout print_test_case z3 name l nargs (i - 1) accu_no_dup'
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
    FStar.IO.print_newline ();
    accu_no_dup
  end

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

noeq
type branch_trace_node =
| Node: value: nat -> children: list branch_trace_node -> branch_trace_node

let assert_valid_state =
  "(assert (or (= state-witness-input-size -1) (= state-witness-input-size 0)))\n"

let rec enumerate_branch_traces'
  (timeout: option nat)
  (z3: Z3.z3)
  (max_depth cur_depth: nat)
  (branch_trace: string)
: ML (list branch_trace_node)
= if max_depth = cur_depth
  then []
  else begin
    z3.to_z3 (Printf.sprintf "(assert (> (branch-index state-witness) %d))\n" cur_depth);
    send_check_sat z3 timeout;
    let status = z3.from_z3 () in
    if status = "sat"
    then
      let rec aux accu choice : ML (list branch_trace_node) =
        let branch_trace' = branch_trace ^ " " ^ string_of_int choice in
        FStar.IO.print_string (Printf.sprintf "Checking feasibility of branch trace: %s\n" branch_trace');
        z3.to_z3 "(push)\n";
        z3.to_z3 (Printf.sprintf "(assert (= (branch-trace %d) %d))\n" cur_depth choice);
        send_check_sat z3 timeout;
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
          send_check_sat z3 timeout;
          let status = z3.from_z3 () in
          z3.to_z3 "(pop)\n";
          if status = "sat"
          then begin
            FStar.IO.print_string "Branch is valid\n";
            let res = enumerate_branch_traces' timeout z3 max_depth (cur_depth + 1) branch_trace' in
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
  timeout
  (z3: Z3.z3)
  (max_depth: nat)
: ML (list branch_trace_node)
= z3.to_z3 "(push)\n";
  let res = enumerate_branch_traces' timeout z3 max_depth 0 "" in
  z3.to_z3 "(pop)\n";
  res

let compute_timeout (timeout: HashingOptions.timeout_options) (allow_unspecified: bool) : ML (option nat) =
  match timeout with
  | HashingOptions.Timeout n -> Some (OS.timestamp () + n)
  | HashingOptions.TimeoutUnlimited -> None
  | _ ->
    if allow_unspecified
    then None
    else failwith "compute_timeout: please specify either --z3_branch_depth n, where n shall be a nonnegative integer, or --z3_global_timeout t, where t shall be a positive integer or 'unlimited'"

let rec want_witnesses_with_depth'
  timeout
  (print_test_case: (Seq.seq int -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) nbwitnesses
  cur_depth (tree: list branch_trace_node) (branch_trace: string)
: ML unit
=
  FStar.IO.print_string (Printf.sprintf "Checking witnesses for branch trace: %s\n" branch_trace);
  let _ : string = want_witnesses timeout print_test_case z3 name l nargs nbwitnesses "" in
  z3.to_z3 (Printf.sprintf "(assert (> (branch-index state-witness) %d))\n" cur_depth);
  let rec aux (tree: list branch_trace_node) : ML unit = match tree with
  | [] -> ()
  | Node choice tree' :: q ->
    z3.to_z3 "(push)\n";
    z3.to_z3 (Printf.sprintf "(assert (= (branch-trace %d) %d))\n" cur_depth choice);
    want_witnesses_with_depth' timeout print_test_case z3 name l nargs nbwitnesses (cur_depth + 1) tree' (branch_trace ^ " " ^ string_of_int choice);
    z3.to_z3 "(pop)\n";
    aux q
  in
  aux tree

let want_witnesses_with_depth timeout =
  let timeout = compute_timeout timeout true in
  want_witnesses_with_depth' timeout

let rec enumerate_branch_traces_for_next_depth'
  timeout
  (z3: Z3.z3)
  (next_depth: nat)
  (cur_depth: nat { cur_depth < next_depth })
  (branch_trace: string)
  (tree: list branch_trace_node)
: ML (list branch_trace_node)
= 
//  FStar.IO.print_string (Printf.sprintf "enumerate_branch_traces_for_next_depth': next_depth = %d, cur_depth = %d, branch_trace = %s\n" next_depth cur_depth branch_trace);
  match tree with
  | [] ->
    if cur_depth + 1 = next_depth
    then enumerate_branch_traces' timeout z3 next_depth cur_depth branch_trace
    else []
  | Node choice tree' :: q ->
    if cur_depth + 1 = next_depth
    then failwith "enumerate_branch_traces_for_next_depth': input tree too large, this should not happen"
    else begin
      let branch_trace' = branch_trace ^ " " ^ string_of_int choice in
      z3.to_z3 "(push)\n";
      z3.to_z3 (Printf.sprintf "(assert (= (branch-trace %d) %d))\n" cur_depth choice);
      let tree'' = enumerate_branch_traces_for_next_depth' timeout z3 next_depth (cur_depth + 1) branch_trace' tree' in
      z3.to_z3 "(pop)\n";
      let q' = enumerate_branch_traces_for_next_depth' timeout z3 next_depth cur_depth branch_trace q in
      // simplify the tree if no branches were found AND we are not at the end of the tree
      if Nil? tree'' && cur_depth + 2 < next_depth
      then q'
      else Node choice tree'' :: q'
    end

let rec want_witnesses_at_leaves
  (timeout: option nat)
  (f: (unit -> ML string))
  (print_test_case: (Seq.seq int -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) nbwitnesses
  max_depth (cur_depth: nat { cur_depth <= max_depth }) (tree: list branch_trace_node) (branch_trace: string) (accu_no_dup: string)
: ML string
=
//  FStar.IO.print_string (Printf.sprintf "want_witnesses_at_leaves: max_depth = %d, cur_depth = %d, branch_trace = %s\n" max_depth cur_depth branch_trace);
  match tree with
  | [] ->
    if cur_depth < max_depth
    then accu_no_dup
    else begin
      FStar.IO.print_string (Printf.sprintf "Checking witnesses for branch trace: %s\n" branch_trace);
      z3.to_z3 "(push)\n";
      z3.to_z3 (f ());
      z3.to_z3 assert_valid_state;
      z3.to_z3 (Printf.sprintf "(assert (>= (branch-index state-witness) %d))\n" cur_depth);
      z3.to_z3 accu_no_dup;
      let new_no_dup = want_witnesses timeout print_test_case z3 name l nargs nbwitnesses accu_no_dup in
      z3.to_z3 "(pop)\n";
      accu_no_dup ^ new_no_dup
    end
  | Node choice tree' :: q ->
    if cur_depth = max_depth
    then
      failwith "want_witnesses_at_leaves: tree is too large. This should not happen"
    else begin
      z3.to_z3 "(push)\n";
      z3.to_z3 (Printf.sprintf "(assert (= (branch-trace %d) %d))\n" cur_depth choice);
      let accu_no_dup1 = want_witnesses_at_leaves timeout f print_test_case z3 name l nargs nbwitnesses max_depth (cur_depth + 1) tree' (branch_trace ^ " " ^ string_of_int choice) accu_no_dup in
      z3.to_z3 "(pop)\n";
      want_witnesses_at_leaves timeout f print_test_case z3 name l nargs nbwitnesses max_depth cur_depth q branch_trace accu_no_dup1
    end

let want_witnesses_indefinitely
  (timeout: HashingOptions.timeout_options)
  (f: (unit -> ML string))
  (print_test_case: (Seq.seq int -> list string -> ML unit)) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) nbwitnesses
: ML unit
= 
  let timeout = compute_timeout timeout false in
  let rec aux
    (cur_depth: nat)
    (tree: list branch_trace_node)
    (accu_no_dup: string)
  : ML unit
  = if Nil? tree && cur_depth > 0
    then
      FStar.IO.print_string "Tree is empty, no more paths to explore.\n"
    else begin
      let accu_no_dup' = want_witnesses_at_leaves timeout f print_test_case z3 name l nargs nbwitnesses cur_depth 0 tree "" accu_no_dup in
      let tree' = enumerate_branch_traces_for_next_depth' timeout z3 (cur_depth + 1) 0 "" tree in
      aux (cur_depth + 1) tree' accu_no_dup'
    end
  in
  aux 0 [] ""

let witnesses_for_depth max_depth (timeout: HashingOptions.timeout_options) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) (print_test_case_mk_get_first_witness: list ((Seq.seq int -> list string -> ML unit) & (unit -> ML string))) nbwitnesses =
  z3.to_z3 "(push)\n";
  z3.to_z3 (mk_get_witness name l);
  let traces = enumerate_branch_traces (compute_timeout timeout true) z3 max_depth in
  z3.to_z3 assert_valid_state;
  List.iter
    #((Seq.seq int -> list string -> ML unit) & (unit -> ML string))
    (fun (ptc, f) ->
      z3.to_z3 "(push)\n";
      z3.to_z3 (f ());
      want_witnesses_with_depth timeout ptc z3 name l nargs nbwitnesses 0 traces "";
      z3.to_z3 "(pop)\n"
    )
    print_test_case_mk_get_first_witness
    ;
  z3.to_z3 "(pop)\n"

let witnesses_for_indefinitely (timeout: HashingOptions.timeout_options) (z3: Z3.z3) (name: string) (l: list arg_type) (nargs: nat { nargs == count_args l }) (print_test_case_mk_get_first_witness: list ((Seq.seq int -> list string -> ML unit) & (unit -> ML string))) nbwitnesses =
  z3.to_z3 "(push)\n";
  z3.to_z3 (mk_get_witness name l);
  List.iter
    #((Seq.seq int -> list string -> ML unit) & (unit -> ML string))
    (fun (ptc, f) ->
      z3.to_z3 "(push)\n";
      want_witnesses_indefinitely timeout f ptc z3 name l nargs nbwitnesses;
      z3.to_z3 "(pop)\n"
    )
    print_test_case_mk_get_first_witness
    ;
  z3.to_z3 "(pop)\n"

let witnesses_for = function
| None -> witnesses_for_indefinitely
| Some depth -> witnesses_for_depth depth

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
    printf(\"Reached from position %ld: type name %s, field name %s\\n\", start_pos, typename_s, fieldname);
  } else {
    printf(\"Parsing failed at position %ld: type name %s, field name %s. Reason: %s\\n\", start_pos, typename_s, fieldname, reason);
    *context = 1;
  }
}
"

let do_test (out_dir: string) (out_file: option string) (z3: Z3.z3) (prog: prog) (name1: string) (nbwitnesses: int) (timeout: HashingOptions.timeout_options) (depth: option nat) (pos: bool) (neg: bool) : ML unit =
  let def = List.assoc name1 prog in
  if None? def
  then failwith (Printf.sprintf "do_test: parser %s not found" name1);
  let args = (Some?.v def).args in
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
  let tasks =
    begin
      if pos
      then [print_witness_as_c out_dir cout true validator_name args counter, (fun _ -> (
        FStar.IO.print_string (Printf.sprintf ";; Positive test witnesses for %s\n" name1);
        mk_get_positive_test_witness name1 args
      ))]
      else []
    end `List.Tot.append`
    begin
      if neg
      then [print_witness_as_c out_dir cout false validator_name args counter, (fun _ -> (
        FStar.IO.print_string (Printf.sprintf ";; Negative test witnesses for %s\n" name1);
        mk_get_negative_test_witness name1 args
      ))]
      else []
    end
  in
  witnesses_for depth timeout z3 name1 args nargs tasks nbwitnesses;
  cout "  return 0;
  }
"
  )

let mk_get_diff_test_witness (name1: string) (l: list arg_type) (name2: string) : string =
  let call2 = mk_call_args name2 0 l in
  Printf.sprintf
"
%s
(define-fun negative-state-witness () State (%s (mk-state initial-input-size 0 -1))) ; branch trace is ignored for the second parser
(assert (not (= (input-size negative-state-witness) 0))) ; test cases that do not consume everything are considered failing
(assert (>= (input-size negative-state-witness) -1)) ; do not record tests that artificially fail due to SMT2 encoding
"
  (mk_get_positive_test_witness name1 l)
  call2

let do_diff_test_for (out_dir: string) (counter: ref int) (cout: string -> ML unit) (z3: Z3.z3) (prog: prog) name1 name2 args (nargs: nat { nargs == count_args args }) validator_name1 validator_name2 nbwitnesses timeout depth =
  FStar.IO.print_string (Printf.sprintf ";; Witnesses that work with %s but not with %s\n" name1 name2);
  witnesses_for depth timeout z3 name1 args nargs ([print_diff_witness_as_c out_dir cout validator_name1 validator_name2 args counter, (fun _ -> mk_get_diff_test_witness name1 args name2)]) nbwitnesses

let do_diff_test (out_dir: string) (out_file: option string) (z3: Z3.z3) (prog: prog) name1 name2 nbwitnesses timeout depth =
  let def = List.assoc name1 prog in
  if None? def
  then failwith (Printf.sprintf "do_diff_test: parser %s not found" name1);
  let args = (Some?.v def).args in
  let def2 = List.assoc name2 prog in
  if None? def2
  then failwith (Printf.sprintf "do_diff_test: parser %s not found" name2);
  if def2 <> def
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
  do_diff_test_for out_dir counter cout z3 prog name1 name2 args nargs validator_name1 validator_name2 nbwitnesses timeout depth;
  do_diff_test_for out_dir counter cout z3 prog name2 name1 args nargs validator_name2 validator_name1 nbwitnesses timeout depth;
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
void * "^arg_var^" = NULL;
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
      printf(\"Cannot read %ld bytes from %s\\n\", len, filename);
      return 3;
    };
    buf = (uint8_t *) vbuf;
  };
  printf(\"Read %ld bytes from %s\\n\", len, filename);
  uint8_t context = 0;
  uint64_t result = "^validator_name^"("^call_args_lhs^"&context, &TestErrorHandler, buf, len, 0);
  if (len > 0)
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
  let def = List.assoc name1 prog in
  if None? def
  then failwith (Printf.sprintf "produce_test_checker_exe: parser %s not found" name1);
  let args = (Some?.v def).args in
  let modul, validator_name = module_and_validator_name name1 in
  with_out_file out_file (fun cout ->
    cout (test_checker_c modul validator_name args)
  )
