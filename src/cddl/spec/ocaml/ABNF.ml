type ('a, 'b, 'c) parser = ('a, 'b) TokenBuffer.t -> 'c option

let stack_level = ref 0

let print_spaces () =
  let spaces = String.make !stack_level ' ' in
  print_string spaces

let debug
      (name: string)
      (f: ('a, 'b, 'c) parser)
    : ('a, 'b, 'c) parser
  = fun buf ->
  print_spaces ();
  print_endline ("Entering: " ^ name);
  incr stack_level;
  let res = f buf in
  decr stack_level;
  print_spaces ();
  begin match res with
  | Some a ->
     print_endline ("Success: " ^ name)
  | None ->
     print_endline ("Failure: " ^ name)
  end;
  res

let debug_start
      (name: string)
      (f: ('a, 'b, 'c) parser)
    : ('a, 'b, 'c) parser
  = fun buf ->
    stack_level := 0;
    debug name f buf

let get_state () : ('a, 'b, 'b) parser =
  fun buf -> Some buf.state

let set_state (x: 'b) : ('a, 'b, unit) parser =
  fun buf -> buf.state <- x; Some ()

let choice
      (f: ('a, 'b, 'c) parser)
      (g: ('a, 'b, 'c) parser)
      (x: ('a, 'b) TokenBuffer.t)
    : 'c option
  = let saved = TokenBuffer.backup x in
    match f x with
    | Some y -> Some y
    | None ->
       TokenBuffer.restore x saved;
       g x

let fail : ('a, 'b, 'c) parser = (fun _ -> None)

let rec choices l = match l with
  | [] -> fail
  | a :: q -> choice a (choices q)

let concat
      (f: ('a, 'b, 'c) parser)
      (g: 'c -> ('a, 'b, 'd) parser)
      (x: ('a, 'b) TokenBuffer.t)
    : 'd option
  = match f x with
  | Some y ->
     incr stack_level;
     let res = g y x in
     decr stack_level;
     res
  | None -> None

let ret
      (x: 'a)
      (y: ('b, 'c) TokenBuffer.t)
    : 'a option
= Some x

let ret_option
      (x: 'a option)
      (y: ('b, 'c) TokenBuffer.t)
    : 'a option
= x

let option
      (f: ('a, 'b, 'c) parser)
    : ('a, 'b, 'c option) parser
= choice (concat f (fun x -> ret (Some x))) (ret None)

let terminal
      (f: 'a -> 'b option)
      (x: ('a, 'c) TokenBuffer.t)
    : 'b option
  = f (TokenBuffer.advance x)

let rec list
          (f: ('a, 'b, 'c) parser)
: ('a, 'b, 'c list) parser
  = choice
      (nonempty_list f)
      (ret [])

and nonempty_list
(f: ('a, 'b, 'c) parser)
    : ('a, 'b, 'c list) parser
  = concat f (fun a -> concat (list f) (fun q -> ret (a :: q)))

let rec ignore_list
      (f: ('a, 'b, 'c) parser)
    : ('a, 'b, unit) parser
  = choice (concat f (fun _ -> ignore_list f)) (ret ())