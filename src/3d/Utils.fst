module Utils
inline_for_extraction
let valid_string
  (valid: (string -> Tot bool))
: Tot Type0
= (s: string { valid s == true })

let always_valid (_: string) : Tot bool = true

let starts_with_capital (s: string) : Tot bool =
  String.length s >= 1 &&
  begin let first = String.sub s 0 1 in
    String.compare first "A" >= 0 && String.compare first "Z" <= 0
  end

let ends_with (s:string) (suffix:string) : bool =
  let l = String.length s in
  let sl = String.length suffix in
  if sl > l || sl = 0
  then false
  else let suffix' = String.sub s (l - sl) sl in
       suffix = suffix'

let string_starts_with (big small: string) : Tot bool =
  let small_len = String.length small in
  if String.length big < small_len
  then false
  else String.sub big 0 small_len = small

