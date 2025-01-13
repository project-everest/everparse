type ('a, 'b) parser = 'a TokenBuffer.t -> 'b option

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
  | Some y -> g y x
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
