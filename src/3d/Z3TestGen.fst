module Z3TestGen
module Printf = FStar.Printf
open FStar.All

let prelude : string =
"
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(define-fun parse-empty ((x (Seq Int))) (Seq (Pair Int Int))
  (seq.unit (mk-pair 0 0))
)

(define-fun parse-u8 ((x (Seq Int))) (Seq (Pair Int Int))
  (if (= (seq.len x) 0)
    (as seq.empty (Seq (Pair Int Int)))
    (seq.unit (mk-pair (seq.nth x 0) 1))
  )
)

(define-fun parse-fail ((x (Seq Int))) (Seq Int)
  (as seq.empty (Seq Int))
)
"

let mk_wrap_parser
  (name: string)
  (binders: string)
  (body: string)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp = Printf.sprintf "%s-tmp" name in
  Printf.sprintf
"(define-fun %s (%s(%s (Seq Int))) (Seq Int)
   (let ((%s (%s %s)))
     (if (= (seq.len %s) 0)
       (as seq.empty (Seq Int))
       (seq.unit (second (seq.nth %s 0)))
     )
   )
 )
"
  name
  binders
  input
  tmp
  body
  input
  tmp
  tmp

let mk_parse_ifthenelse
  (name: string)
  (binders: string)
  (cond: string)
  (f_then: string)
  (f_else: string)
: string
= let input = Printf.sprintf "%s-input" name in
  Printf.sprintf
"(define-fun %s (%s(%s (Seq Int))) (Seq Int)
   (if %s
     (%s %s)
     (%s %s)
   )
 )
"
  name
  binders
  input
  cond
  f_then
  input
  f_else
  input

let mk_parse_dtuple2
  (name: string)
  (binders: string)
  (dfst: string)
  (new_binder_name: string)
  (dsnd: string) (* already contains the new argument *)
: string
= let input = Printf.sprintf "%s-input" name in
  let tmp_has_tag = Printf.sprintf "%s-tmp-has-tag" name in
  let tmp_tag_result = Printf.sprintf "%s-tmp-tag-result" name in
  let tmp_payload = Printf.sprintf "%s-tmp-payload" name in
  Printf.sprintf
"(define-fun %s (%s(%s (Seq Int))) (Seq Int)
   (let ((%s (%s %s)))
     (if (= (seq.len %s) 0)
       (as seq.empty (Seq Int))
       (let ((%s (seq.nth %s 0)))
         (let ((%s (first %s)))
           (let ((%s (%s (seq.extract %s (second %s) (- (seq.len %s) (second %s))))))
             (if (= (seq.len %s) 0)
               (as seq.empty (Seq Int))
               (seq.unit (+ (second %s) (seq.nth %s 0)))
             )
           )
         )
       )
     )
   )
 )"
  name
  binders
  input
  tmp_has_tag
  dfst
  input
  tmp_has_tag
  tmp_tag_result
  tmp_has_tag
  new_binder_name
  tmp_tag_result
  tmp_payload
  dsnd
  input
  tmp_tag_result
  input
  tmp_tag_result
  tmp_payload
  tmp_tag_result
  tmp_payload

type binders = {
  bind: string;
  args: string;
}

let empty_binders : binders = {
  bind = "";
  args = "";
}

let push_binder (name: string) (typ: string) (b: binders) : binders = {
  bind = Printf.sprintf "(%s %s) %s" name typ b.bind;
  args = Printf.sprintf " %s%s" name b.args;
}

let mk_function_call (name: string) (b: binders) =
  Printf.sprintf "%s%s" name b.args

type reading = { call: string }
type not_reading = { call: string }

type parser (a: Type) =
  (* name *) string ->
  (* binders *) binders ->
  (* out *) (string -> ML unit) ->
  ML a

let parse_u8 : parser reading =
  fun _ _ _ -> { call = "parse-u8" }

let parse_empty : parser reading =
  fun _ _ _ -> { call = "parse-empty" }

let parse_fail : parser not_reading =
  fun _ _ _ -> { call = "parse-fail" }

let wrap_parser (p: parser reading) : parser not_reading =
  fun name binders out ->
    let name' = Printf.sprintf "%s-wrapped" name in
    let body = p name' binders out in
    out (mk_wrap_parser name binders.bind body.call);
    { call = mk_function_call name binders }

let parse_ifthenelse (cond: string) (pthen: parser not_reading) (pelse: parser not_reading) =
  fun name binders out ->
    let name_then = Printf.sprintf "%s-then" name in
    let body_then = pthen name_then binders out in
    let name_else = Printf.sprintf "%s-else" name in
    let body_else = pelse name_else binders out in
    out (mk_parse_ifthenelse name binders.bind cond body_then.call body_else.call);
    { call = mk_function_call name binders }

let parse_dtuple2 (tag: parser reading) (new_binder: string) (payload: parser not_reading) : parser not_reading =
  fun name binders out ->
    let name_tag = Printf.sprintf "%s-tag" name in
    let body_tag = tag name_tag binders out in
    let binders' = push_binder new_binder "Int" binders in (* TODO: support more types *)
    let name_payload = Printf.sprintf "%s-payload" name in
    let body_payload = payload name_payload binders' out in
    out (mk_parse_dtuple2 name binders.bind body_tag.call new_binder body_payload.call);
    { call = mk_function_call name binders }

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

let mk_get_first_witness (name1: string) (name2: string) : string =
  Printf.sprintf
"
(push)
(assert (and (= (seq.len (%s witness)) 1) (= (seq.len (%s witness)) 0)))
(check-sat)
"
  name1
  name2


let read_witness (z3: Z3.z3) =
  Lisp.read_witness_from z3.from_z3

let mk_want_another_witness letbinding p =
  Printf.sprintf
"(assert (not (= (seq.extract witness 0 (seq.nth (%s witness) 0)) (let %s (seq.extract witness 0 (seq.nth (%s witness) 0))))))
 (check-sat)
"
  p
  letbinding
  p

let rec want_other_witnesses (z3: Z3.z3) p i : ML unit =
  let status = z3.from_z3 () in
  if status = "sat" then begin
    z3.to_z3 "(get-value (witness))\n";
    let (letbinding, _) = read_witness z3 in
    if i <= 0
    then ()
    else begin
      z3.to_z3 (mk_want_another_witness letbinding p);
      want_other_witnesses z3 p (i - 1)
    end
  end

let witnesses_for (z3: Z3.z3) name1 name2 extra =
  FStar.IO.print_string (Printf.sprintf ";; Witnesses that work with %s but not with %s\n" name1 name2);
  z3.to_z3 (mk_get_first_witness name1 name2);
  want_other_witnesses z3 name1 extra;
  z3.to_z3 "(pop)\n"

let diff_test (p1: parser not_reading) name1 (p2: parser not_reading) name2 extra =
  let buf : ref string = alloc "" in
  let out x : ML unit = buf := Printf.sprintf "%s%s" !buf x in
  let name1 = (p1 name1 empty_binders out).call in
  let name2 = (p2 name2 empty_binders out).call in
  Z3.with_z3 (fun z3 ->
    z3.to_z3 prelude;
    z3.to_z3 !buf;
    z3.to_z3 interlude;
    witnesses_for z3 name1 name2 extra;
    witnesses_for z3 name2 name1 extra
  )

(*
let _ =
  let test1 = parse_dtuple2 parse_u8 "x" (parse_ifthenelse "(< x 12)" parse_fail (parse_dtuple2 parse_u8 "y" (parse_ifthenelse "(> (+ x y) 28)" parse_fail (wrap_parser parse_empty)))) in
  let test2 = parse_dtuple2 parse_u8 "x" (parse_ifthenelse "(< x 10)" parse_fail (parse_dtuple2 parse_u8 "y" (parse_ifthenelse "(> (+ x y) 30)" parse_fail (wrap_parser parse_u8)))) in
  diff_test test1 "test1" test2 "test2" 5
