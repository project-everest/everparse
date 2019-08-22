module H = BatHashtbl
type ('key, 'value) t = ('key, 'value) H.t

let create i = H.create (Z.to_int i)
let try_find = H.find_option
let insert = H.add
let remove = H.remove
let fold = H.fold
