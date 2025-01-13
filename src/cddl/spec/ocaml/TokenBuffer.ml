type 'a t = {
    get: (unit -> 'a);
    mutable past: 'a list;
    mutable future: 'a list;
  }

let create (get: (unit -> 'a)) : 'a t =
  {
    get = get;
    past = [];
    future = [];
  }

let backup (x: 'a t) = List.length x.past

let restore (x: 'a t) (to_past_len: int) : unit =
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
  aux (List.length x.past)
  
let advance (x: 'a t) : 't =
  let a = match x.future with
  | a :: q ->
     x.future <- q;
     a
  | [] -> x.get ()
  in
  x.past <- a :: x.past;
  a
