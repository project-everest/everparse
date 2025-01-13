type ('a, 'b) parser = 'a TokenBuffer.t -> 'b option

let stack_level = ref 0

let print_spaces () =
  let spaces = String.make !stack_level ' ' in
  print_string spaces

let debug
      (name: string)
      (f: ('a, 'b) parser)
    : ('a, 'b) parser
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
      (f: ('a, 'b) parser)
    : ('a, 'b) parser
  = fun buf ->
    stack_level := 0;
    debug name f buf

let choice
      (f: 'b TokenBuffer.t -> 'a option)
      (g: 'b TokenBuffer.t -> 'a option)
      (x: 'b TokenBuffer.t)
    : 'a option
  = let saved = TokenBuffer.backup x in
    match f x with
    | Some y -> Some y
    | None ->
       TokenBuffer.restore x saved;
       g x

let fail : ('a, 'b) parser = (fun _ -> None)

let rec choices l = match l with
  | [] -> fail
  | a :: q -> choice a (choices q)

let concat
      (f: 'b TokenBuffer.t -> 'a option)
      (g: 'a -> 'b TokenBuffer.t -> 'c option)
      (x: 'b TokenBuffer.t)
    : 'c option
  = match f x with
  | Some y ->
     incr stack_level;
     let res = g y x in
     decr stack_level;
     res
  | None -> None

let ret
      (x: 'a)
      (y: 'b TokenBuffer.t)
    : 'a option
= Some x

let option
      (f: ('a, 'b) parser)
    : ('a, 'b option) parser
= choice (concat f (fun x -> ret (Some x))) (ret None)

let terminal
      (f: 'a -> 'b option)
      (x: 'a TokenBuffer.t)
    : 'b option
  = f (TokenBuffer.advance x)

let rec list
          (f: ('a, 'b) parser)
: ('a, 'b list) parser
  = choice
      (nonempty_list f)
      (ret [])

and nonempty_list
(f: ('a, 'b) parser)
    : ('a, 'b list) parser
  = concat f (fun a -> concat (list f) (fun q -> ret (a :: q)))

let rec ignore_list
      (f: ('b, 'a) parser)
    : ('b, unit) parser
  = choice (concat f (fun _ -> ignore_list f)) (ret ())
