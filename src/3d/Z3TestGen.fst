module Z3TestGen
module Printf = FStar.Printf
open FStar.All

module A = Ast
module T = Target
module I = InterpreterTarget

let prelude : string =
"
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(define-fun parse-empty ((x (Seq Int))) (Seq (Pair Int Int))
  (seq.unit (mk-pair 0 0))
)

(define-fun parse-u8 ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 1)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit (mk-pair (seq.nth x 0) 1))
  )
)

(define-fun parse-u16-be ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 2)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit 
      (mk-pair
        (+ (seq.nth x 1)
          (* 256
            (seq.nth x 0)
          )
        )
        2
      )
    )
  )
)

(define-fun parse-u16-le ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 2)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit 
      (mk-pair
        (+ (seq.nth x 0)
          (* 256
            (seq.nth x 1)
          )
        )
        2
      )
    )
  )
)

(define-fun parse-u32-be ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 4)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit 
      (mk-pair
        (+ (seq.nth x 3)
          (* 256
            (+ (seq.nth x 2)
              (* 256
                (+ (seq.nth x 1)
                  (* 256
                    (seq.nth x 0)
                  )
                )
              )
            )
          )
        )
        4
      )
    )
  )
)

(define-fun parse-u32-le ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 4)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit 
      (mk-pair
        (+ (seq.nth x 0)
          (* 256
            (+ (seq.nth x 1)
              (* 256
                (+ (seq.nth x 2)
                  (* 256
                    (seq.nth x 3)
                  )
                )
              )
            )
          )
        )
        4
      )
    )
  )
)

(define-fun parse-u64-be ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 8)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit 
      (mk-pair
        (+ (seq.nth x 7)
          (* 256
            (+ (seq.nth x 6)
              (* 256
                (+ (seq.nth x 5)
                  (* 256
                    (+ (seq.nth x 4)
                      (* 256
                        (+ (seq.nth x 3)
                          (* 256
                            (+ (seq.nth x 2)
                              (* 256
                                (+ (seq.nth x 1)
                                  (* 256
                                    (seq.nth x 0)
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
        8
      )
    )
  )
)

(define-fun parse-u64-le ((x (Seq Int))) (Seq (Pair Int Int))
  (if (< (seq.len x) 8)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit 
      (mk-pair
        (+ (seq.nth x 0)
          (* 256
            (+ (seq.nth x 1)
              (* 256
                (+ (seq.nth x 2)
                  (* 256
                    (+ (seq.nth x 3)
                      (* 256
                        (+ (seq.nth x 4)
                          (* 256
                            (+ (seq.nth x 5)
                              (* 256
                                (+ (seq.nth x 6)
                                  (* 256
                                    (seq.nth x 7)
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
        8
      )
    )
  )
)

(define-fun parse-false ((x (Seq Int))) (Seq Int)
  (as seq.empty (Seq Int))
)

(define-fun parse-all-bytes ((x (Seq Int))) (Seq Int)
  (seq.unit (seq.len x))
)

(define-fun parse-all-zeros ((x (Seq Int))) (Seq Int)
  (if
    (forall ((i Int))
      (if (and (<= 0 i) (< i (seq.len x)))
        (= (seq.nth x i) 0)
        true
      )
    )
    (seq.unit (seq.len x))
    (as seq.empty (Seq Int))
  )
)
"

let mk_constant = function
  | A.Unit -> "0"
  | A.Int _ x -> string_of_int x
  | A.XInt _ x -> x
  | A.Bool true -> "true"
  | A.Bool false -> "false"

let mk_app fn = function
  | None -> fn
  | Some args -> Printf.sprintf "(%s %s)" fn args

let assert_some = function
  | None -> failwith "assert_some"
  | Some x -> x

let mk_op : T.op -> option string -> ML string = function
  | T.Eq -> mk_app "="
  | T.Neq -> (fun s -> mk_app "not" (Some (mk_app "=" s)))
  | T.And -> mk_app "and"
  | T.Or -> mk_app "or"
  | T.Not -> mk_app "not"
  | T.Plus _ -> mk_app "+"
  | T.Minus _ -> mk_app "-"
  | T.Mul _ -> mk_app "*"
  | T.Division _ -> mk_app "/"
  | T.Remainder _ -> mk_app "%"
  | T.LT _ -> mk_app "<"
  | T.GT _ -> mk_app ">"
  | T.LE _ -> mk_app "<="
  | T.GE _ -> mk_app ">="
  | T.IfThenElse -> mk_app "if"
  | T.Cast _ _ -> assert_some (* casts allowed only if they are proven not to lose precision *)
  | T.Ext s -> mk_app s
  | _ -> fun _ -> failwith "mk_op: not supported"

let ident_to_string = A.ident_to_string

let rec mk_expr (e: T.expr) : ML string = match fst e with
  | T.Constant c -> mk_constant c
  | T.Identifier i -> ident_to_string i
  | T.App hd args -> mk_op hd (mk_args args)
  | _ -> failwith "mk_expr: not supported"

and mk_args_aux accu : (list T.expr -> ML string) = function
  | [] -> accu
  | a :: q -> mk_args_aux (Printf.sprintf "%s %s" accu (mk_expr a)) q

and mk_args (l: list T.expr) : ML (option string) = match l with
  | [] -> None
  | a :: q -> Some (mk_args_aux (mk_expr a) q)

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

let parse_u8 : parser reading =
  fun _ _ _ _ -> { call = "parse-u8" }

let parse_u16_be : parser reading =
  fun _ _ _ _ -> { call = "parse-u16-be" }

let parse_u16_le : parser reading =
  fun _ _ _ _ -> { call = "parse-u16-le" }

let parse_u32_be : parser reading =
  fun _ _ _ _ -> { call = "parse-u32-be" }

let parse_u32_le : parser reading =
  fun _ _ _ _ -> { call = "parse-u32-le" }

let parse_u64_be : parser reading =
  fun _ _ _ _ -> { call = "parse-u64-be" }

let parse_u64_le : parser reading =
  fun _ _ _ _ -> { call = "parse-u64-le" }

let parse_empty : parser reading =
  fun _ _ _ _ -> { call = "parse-empty" }

let parse_readable_itype (i: I.readable_itype) = match i with
  | I.UInt8 | I.UInt8BE -> parse_u8
  | I.UInt16 -> parse_u16_le
  | I.UInt16BE -> parse_u16_be
  | I.UInt32 -> parse_u32_le
  | I.UInt32BE -> parse_u32_be
  | I.UInt64 -> parse_u64_le
  | I.UInt64BE -> parse_u64_be
  | I.Unit -> parse_empty

let mk_wrap_parser
  (name: string)
  (binders: string)
  (body: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
   (let (("^tmp^" ("^body^" "^input^")))
     (if (= (seq.len "^tmp^") 0)
       (as seq.empty (Seq Int))
       (seq.unit (second (seq.nth "^tmp^" 0)))
     )
   )
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
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
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
  mk_args_aux (ident_to_string id) args
  
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
= fun _ _ _ _ -> { call = mk_app_without_paren hd args }

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
  let tmp_has_fst = Printf.sprintf "%s-tmp-has-fst" name in
  let tmp_fst = Printf.sprintf "%s-tmp-fst" name in
  let tmp_snd_result = Printf.sprintf "%s-tmp-snd-result" name in
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
   (let (("^tmp_has_fst^" ("^fst^" "^input^")))
     (if (= (seq.len "^tmp_has_fst^") 0)
       (as seq.empty (Seq Int))
       (let (("^tmp_fst^" (seq.nth "^tmp_has_fst^" 0)))
         (let (("^tmp_snd_result^" ("^snd^" (seq.extract "^input^" "^tmp_fst^" (- (seq.len "^input^") "^tmp_fst^")))))
           (if (= (seq.len "^tmp_snd_result^") 0)
             (as seq.empty (Seq Int))
             (seq.unit (+ "^tmp_fst^" (seq.nth "^tmp_snd_result^" 0)))
           )
         )
       )
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
  let tmp_has_tag = Printf.sprintf "%s-tmp-has-tag" name in
  let tmp_tag_result = Printf.sprintf "%s-tmp-tag-result" name in
  let tmp_payload = Printf.sprintf "%s-tmp-payload" name in
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
   (let (("^tmp_has_tag^" ("^dfst^" "^input^")))
     (if (= (seq.len "^tmp_has_tag^") 0)
       (as seq.empty (Seq Int))
       (let (("^tmp_tag_result^" (seq.nth "^tmp_has_tag^" 0)))
         (if (let (("^cond_binder_name^" (first "^tmp_tag_result^"))) "^cond^")
           (let (("^dsnd_binder_name^" (first "^tmp_tag_result^")))
             (let (("^tmp_payload^" ("^dsnd^" (seq.extract "^input^" (second "^tmp_tag_result^") (- (seq.len "^input^") (second "^tmp_tag_result^"))))))
               (if (= (seq.len "^tmp_payload^") 0)
                 (as seq.empty (Seq Int))
                 (seq.unit (+ (second "^tmp_tag_result^") (seq.nth "^tmp_payload^" 0)))
               )
             )
           )
           (as seq.empty (Seq Int))
         )
       )
     )
   )
 )"

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
  parse_dep_pair_with_refinement tag cond_binder cond cond_binder (wrap_parser parse_empty)

let mk_parse_ifthenelse
  (name: string)
  (binders: string)
  (cond: string)
  (f_then: string)
  (f_else: string)
: string
= let input = Printf.sprintf "%s-input" name in
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
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
"(define-fun "^name^" ("^binders^"("^input^" (Seq Int))) (Seq Int)
  (let (("^sz^" "^size^"))
    (if (< (seq.len "^input^") "^sz^")
      (as seq.empty (Seq Int))
      (let (("^res^" ("^body^" (seq.extract "^input^" 0 "^sz^"))))
        (if (= (seq.len "^res^") 0)
          (as seq.empty (Seq Int))
          (if (= (seq.nth "^res^" 0) "^sz^")
            "^res^"
            (as seq.empty (Seq Int))
          )
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

let rec parse_typ : I.typ -> parser not_reading = function
  | I.T_false _ -> parse_false
  | I.T_denoted _ d
  | I.T_with_dep_action _ d _ -> parse_denoted d
  | I.T_pair _ t1 t2 -> parse_pair (parse_typ t1) (parse_typ t2)
  | I.T_dep_pair _ t1 (lam, t2)
  | I.T_dep_pair_with_action _ t1 (lam, t2) _ -> parse_dep_pair (parse_readable_dtyp t1) lam (parse_typ t2)
  | I.T_refine _ base (lam, cond)
  | I.T_refine_with_action _ base (lam, cond) _ -> parse_refine (parse_readable_dtyp base) lam (fun _ -> mk_expr cond)
  | I.T_dep_pair_with_refinement _ base (lam_cond, cond) (lam_k, k)
  | I.T_dep_pair_with_refinement_and_action _ base (lam_cond, cond) (lam_k, k) _ -> parse_dep_pair_with_refinement (parse_readable_dtyp base) lam_cond (fun _ -> mk_expr cond) lam_k (parse_typ k)
  | I.T_if_else cond t1 t2 -> parse_ifthenelse (fun _ -> mk_expr cond) (parse_typ t1) (parse_typ t2)
  | I.T_with_action _ base _
  | I.T_with_comment _ base _ -> parse_typ base
  | I.T_at_most _ size body -> parse_at_most (fun _ -> mk_expr size) (parse_typ body)
  | I.T_exact _ size body -> parse_exact (fun _ -> mk_expr size) (parse_typ body)
  | I.T_string _ _ _ -> unsupported_parser "T_string" _
  | I.T_nlist _ _ _ -> unsupported_parser "T_nlist" _

let smt_type_of_typ (t: T.typ) : Tot string =
  "Int" (* TODO: support more cases, such as booleans *)

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

let produce_type_decl (a: I.type_decl) (out: string -> ML unit) : ML unit =
  let binders = binders_of_params a.name.td_params in
  let _ = parse_typ a.typ (ident_to_string a.name.td_name) binders true out in
  ()

let produce_decl (a: I.decl) : (out: string -> ML unit) -> ML unit =
  match a with
  | Inl a -> produce_not_type_decl a
  | Inr a -> produce_type_decl a

let produce_decls (l: list I.decl) (out: string -> ML unit) : ML unit =
  List.iter (fun a -> produce_decl a out) l

let interlude =
"
(declare-const witness (Seq Int))
(assert (forall ((j Int))
  (if (and (<= 0 j) (< j (seq.len witness)))
    (let ((witnessj (seq.nth witness j)))
      (and (<= 0 witnessj) (< witnessj 256))
    )
    true
  )
))
"

let produce_prog (l: list I.decl) (out: string -> ML unit) : ML unit =
  out prelude;
  produce_decls l out;
  out interlude

(* Produce the SMT2 encoding of the parser spec *)

let print_prog (l: list I.decl) =
  produce_prog l FStar.IO.print_string

let with_out_file
  (#a: Type)
  (name: string)
  (body: ((string -> ML unit) -> ML a))
: ML a
= let fd = FStar.IO.open_write_file name in
  let res = body (FStar.IO.write_string fd) in
  FStar.IO.close_write_file fd;
  res

let write_prog_to_file (filename: string) (l: list I.decl) : ML unit =
  with_out_file filename (produce_prog l)

(* Ask Z3 for test witnesses *)

let read_witness (z3: Z3.z3) =
  Lisp.read_witness_from z3.from_z3

let rec want_witnesses (z3: Z3.z3) (mk_want_another_witness: string -> string) i : ML unit =
  z3.to_z3 "(check-sat)\n";
  let status = z3.from_z3 () in
  if status = "sat" then begin
    z3.to_z3 "(get-value (witness))\n";
    let (letbinding, _) = read_witness z3 in
    if i <= 1
    then ()
    else begin
      z3.to_z3 (mk_want_another_witness letbinding);
      want_witnesses z3 mk_want_another_witness (i - 1)
    end
  end
  else begin
    FStar.IO.print_string
      begin
        if status = "unsat"
        then";; unsat: no more witnesses"
        else Printf.sprintf ";; %s: z3 gave up" status
      end;
    FStar.IO.print_newline ()
  end

let witnesses_for (z3: Z3.z3) mk_get_first_witness mk_want_another_witness nbwitnesses =
  z3.to_z3 "(push)\n";
  z3.to_z3 mk_get_first_witness;
  want_witnesses z3 mk_want_another_witness nbwitnesses;
  z3.to_z3 "(pop)\n"

let mk_get_first_positive_test_witness (name1: string) : string =
  Printf.sprintf
"
(assert (= (seq.len (%s witness)) 1))
"
  name1

let mk_want_another_positive_witness p letbinding =
  Printf.sprintf
"(assert (not (= (seq.extract witness 0 (seq.nth (%s witness) 0)) (let %s (seq.extract witness 0 (seq.nth (%s witness) 0))))))
"
  p
  letbinding
  p

let mk_get_first_negative_test_witness (name1: string) : string =
  Printf.sprintf
"
(assert (= (seq.len (%s witness)) 0))
"
  name1

let mk_want_another_distinct_witness letbinding =
  Printf.sprintf
"(assert (not (= witness (let %s witness))))
"
  letbinding

let do_test (z3: Z3.z3) (name1: string) (nbwitnesses: int) =
  FStar.IO.print_string (Printf.sprintf ";; Positive test witnesses for %s\n" name1);
  witnesses_for z3 (mk_get_first_positive_test_witness name1) (mk_want_another_positive_witness name1) nbwitnesses;
  FStar.IO.print_string (Printf.sprintf ";; Negative test witnesses for %s\n" name1);
  witnesses_for z3 (mk_get_first_negative_test_witness name1) mk_want_another_distinct_witness nbwitnesses

let mk_get_first_diff_test_witness (name1: string) (name2: string) : string =
  Printf.sprintf
"
(assert (and (= (seq.len (%s witness)) 1) (= (seq.len (%s witness)) 0)))
"
  name1
  name2

let do_diff_test_for (z3: Z3.z3) name1 name2 nbwitnesses =
  FStar.IO.print_string (Printf.sprintf ";; Witnesses that work with %s but not with %s\n" name1 name2);
  witnesses_for z3 (mk_get_first_diff_test_witness name1 name2) (mk_want_another_positive_witness name1) nbwitnesses

let do_diff_test (z3: Z3.z3) name1 name2 nbwitnesses =
  do_diff_test_for z3 name1 name2 nbwitnesses;
  do_diff_test_for z3 name2 name1 nbwitnesses

let diff_test (p1: parser not_reading) name1 (p2: parser not_reading) name2 nbwitnesses =
  let buf : ref string = alloc "" in
  let out x : ML unit = buf := Printf.sprintf "%s%s" !buf x in
  let name1 = (p1 name1 empty_binders false out).call in
  let name2 = (p2 name2 empty_binders false out).call in
  Z3.with_z3 true (fun z3 ->
    z3.to_z3 prelude;
    z3.to_z3 !buf;
    z3.to_z3 interlude;
    do_diff_test z3 name1 name2 nbwitnesses
  )
