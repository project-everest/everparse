// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp
// See the 'F# Tutorial' project for more help.

module Program

let check_inplace_hashes_f h file_c =
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

[<EntryPoint>]
let main _ =
  (* Parse command-line options. This action is only accumulating values into globals, without any further action (other than --help and --version, which interrupt the execution.) *)
  let _ = Options.parse_cmd_line() in
  (* Special mode: --check_inplace_hashes *)
  let inplace_hashes = Options.check_inplace_hashes () in
  if not (List.isEmpty inplace_hashes)
  then
    Hashing_Hash.check_inplace_hashes check_inplace_hashes_f inplace_hashes
    0
  else
    System.Console.WriteLine "You are trying to call the EverParse/3d inplace hash checker with an unsupported EverParse/3d option. The only supported option is --check_inplace_hash . Otherwise, please download and use a full EverParse binary package from https://github.com/project-everest/everparse/releases"
    1
