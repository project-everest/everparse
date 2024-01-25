// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp
// See the 'F# Tutorial' project for more help.

module Program

let check_inplace_hashes file_3d files_c =
  let f h file_c =
    let arr = System.IO.File.ReadAllLines(file_c)
    let len = arr.Length
    (* Check fails if a bad hash or no hash is found. A
       good hash alone does not make the check succeed *)
    let rec aux accu i =
      if i = len
      then accu
      else
        let r = arr.[i].Trim().Split(':')
        let j = i + 1
        if (r.Length <> 2)
        then aux accu j
        else if r.[0] <> Hashing_Hash.c_comment_intro
        then aux accu j
        else if r.[1] = h
        then aux (Some true) j
        else
          let msg = System.String.Concat("Weak hash check failed in ", file_c)
          let msg = System.String.Concat(msg, ", expected ")
          let msg = System.String.Concat(msg, h)
          let msg = System.String.Concat(msg, ", found ")
          let msg = System.String.Concat(msg, r.[1])
          System.Console.WriteLine msg
          Some false
     in
     match aux None 0 with
     | None ->
       System.Console.WriteLine (System.String.Concat ("No hash found in ", file_c))
       false
     | Some res -> res
  in
  Hashing_Hash.check_inplace_hashes f file_3d files_c

// Define a function to construct a message to print
let from whom =
    sprintf "from %s" whom

[<EntryPoint>]
let main argv =
    let message = from "F#" // Call the function
    printfn "Hello world %s" message
    0 // return an integer exit code
