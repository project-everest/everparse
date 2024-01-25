module OS

let dirname (s: string) =
    System.IO.Path.GetDirectoryName(s)

let basename (s: string) =
    System.IO.Path.GetFileName(s)

let extension (s: string) =
    System.IO.Path.GetExtension(s)

let remove_extension (s: string) =
    System.IO.Path.GetFileNameWithoutExtension(s)

let concat (d: string) (f: string) =
    System.IO.Path.Combine(d, f)

let int_of_string (s: string) =
    let r = ref 0
    if System.Int32.TryParse(s, r)
    then !r
    else 0
