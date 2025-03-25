type ('a, 'b) t = {
    get: (unit -> 'a);
    mutable past: 'a list;
    mutable future: 'a list;
    mutable state: 'b;
  }

let create (get: (unit -> 'a)) (state: 'b) : ('a, 'b) t =
  {
    get = get;
    past = [];
    future = [];
    state = state;
  }

let backup (x: ('a, 'b) t) = (x.state, List.length x.past)

let restore (x: ('a, 'b) t) (state_to_past_len: 'b * int) : unit =
  let (state, to_past_len) = state_to_past_len in
  let rec aux len =
    if len = to_past_len
    then ()
    else if len < to_past_len
    then begin
        let a :: q = x.future in
        x.future <- q;
        x.past <- a :: x.past;
        aux (len + 1)
      end else begin
        let a :: q = x.past in
        x.past <- q;
        x.future <- a :: x.future;
        aux (len - 1)
      end
  in
  x.state <- state;
  aux (List.length x.past)
  
let advance (x: ('a, 'b) t) : 'a =
  let a = match x.future with
  | a :: q ->
     x.future <- q;
     a
  | [] -> x.get ()
  in
  x.past <- a :: x.past;
  a
