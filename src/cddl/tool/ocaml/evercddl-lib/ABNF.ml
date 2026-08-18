type ('a, 'b, 'c, 'd) parser = ('a, 'b) TokenBuffer.t -> ('c -> 'd option) -> 'd option

let stack_level = ref 0

let print_spaces () =
  let spaces = String.make !stack_level ' ' in
  print_string spaces

let enable_debug = false

let debug
      (name: string)
      (f: ('a, 'b, 'c, 'd) parser)
    : ('a, 'b, 'c, 'd) parser
  = fun buf k ->
  if enable_debug
  then begin
      print_spaces ();
      print_endline ("Entering: " ^ name);
    end;
  incr stack_level;
  let res = f buf k in
  decr stack_level;
  if enable_debug
  then begin
      print_spaces ();
      match res with
      | Some a ->
         print_endline ("Success: " ^ name)
      | None ->
         print_endline ("Failure: " ^ name)
    end;
  res

let debug_start
      (name: string)
      (f: ('a, 'b, 'c, 'd) parser)
    : ('a, 'b, 'c, 'd) parser
  = fun buf k ->
    stack_level := 0;
    debug name f buf k

let get_state () : ('a, 'b, 'b, 'd) parser =
  fun buf k -> k (TokenBuffer.get_state buf)

let set_state (x: 'b) : ('a, 'b, unit, 'd) parser =
  fun buf k -> TokenBuffer.set_state x buf; k ()

let choice
      (f: ('a, 'b, 'c, 'd) parser)
      (g: ('a, 'b, 'c, 'd) parser)
    : ('a, 'b, 'c,  'd) parser
= fun x k ->
  let saved = TokenBuffer.backup x in
    match f x k with
    | Some y -> Some y
    | None ->
       TokenBuffer.restore x saved;
       g x k

let fail : ('a, 'b, 'c, 'd) parser = (fun _ _ -> None)

let rec choices l = match l with
  | [] -> fail
  | a :: q -> choice a (choices q)

let concat
      (f: ('a, 'b, 'c, 'e) parser)
      (g: 'c -> ('a, 'b, 'd, 'e) parser)
    : ('a, 'b, 'd, 'e) parser
= fun x k ->
  f x (fun y ->
     incr stack_level;
     let res = g y x k in
     decr stack_level;
     res
    )

let ret
      (x: 'a)
    : ('b, 'c, 'a, 'd) parser
= fun y k -> k x

let ret_option
      (x: 'a option)
    : ('b, 'c, 'a, 'd) parser
  = fun y k -> match x with
             | None -> None
             | Some x' -> k x'

let option
      (f: ('a, 'b, 'c, 'd) parser)
    : ('a, 'b, 'c option, 'd) parser
= choice (concat f (fun x -> ret (Some x))) (ret None)

let terminal
      (f: 'a -> 'b option)
    : ('a, 'c, 'b, 'd) parser
= fun x k ->
  match f (TokenBuffer.advance x) with
  | Some y -> k y
  | None -> None

let get_history_length () : ('a, 'b, int, 'd) parser =
  fun buf k -> k (TokenBuffer.history_length buf)

let nonempty
          (f: ('a, 'b, 'c, 'd) parser)
: ('a, 'b, 'c, 'd) parser
= concat (get_history_length ()) (fun len ->
      concat f (fun res ->
          concat (get_history_length ()) (fun len' ->
              if len < len'
              then ret res
              else fail
            )
        )
    )

let rec list
          (f: ('a, 'b, 'c, 'd) parser)
: ('a, 'b, 'c list, 'd) parser
  = choice
      (nonempty_list f)
      (ret [])

and nonempty_list
(f: ('a, 'b, 'c, 'd) parser)
    : ('a, 'b, 'c list, 'd) parser
  = concat (nonempty f) (fun a -> concat (list f) (fun q -> ret (a :: q)))

let rec fold_left
          (f: ('a, 'b, ('c -> 'c), 'd) parser)
: ('a, 'b, ('c -> 'c), 'd) parser
  = choice
      (nonempty_fold_left f)
      (ret (fun x -> x))

and nonempty_fold_left
(f: ('a, 'b, ('c -> 'c), 'd) parser)
    : ('a, 'b, ('c -> 'c), 'd) parser
  = concat f (fun a -> concat (fold_left f) (fun q -> ret (fun x -> q (a x))))

let nonempty_unit_fold_left
      (f: ('a, 'b, unit, 'd) parser)
    : ('a, 'b, unit, 'd) parser
= concat (nonempty_fold_left (concat f (fun _ -> ret (fun x -> x)))) (fun _ -> ret ())

let rec ignore_list
      (f: ('a, 'b, 'c, 'd) parser)
    : ('a, 'b, unit, 'd) parser
  = choice (concat f (fun _ -> ignore_list f)) (ret ())
