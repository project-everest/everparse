// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp
// See the 'F# Tutorial' project for more help.

module HashCheck

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

let load_hash (file: string) (is_weak: bool) : FStar_Pervasives_Native.option<string> =
  use fs = new System.IO.FileStream(file, System.IO.FileMode.Open, System.IO.FileAccess.Read)
  use js = System.Text.Json.JsonDocument.Parse(fs)
  let root = js.RootElement
  if root.ValueKind <> System.Text.Json.JsonValueKind.Object
  then
    FStar_Pervasives_Native.None
  else
    let s = root.GetProperty(System.String.Concat((if is_weak then "weak" else "strong"), "-hash"))
    FStar_Pervasives_Native.Some (s.GetString())

[<EntryPoint>]
let main _ =
  (* Parse command-line options. This action is only accumulating values into globals, without any further action (other than --help and --version, which interrupt the execution.) *)
  let cmd_line_files = Options_Base.parse_cmd_line() in
  (* Special mode: --check_inplace_hashes *)
  let inplace_hashes = Options_Base.check_inplace_hashes () in
  if not (List.isEmpty inplace_hashes)
  then
    Hashing_Hash.check_inplace_hashes check_inplace_hashes_f inplace_hashes
    exit 0
  let out_dir = Options_Base.output_dir () in
  (* Special mode: --check_hashes *)
  match Options_Base.check_hashes () with
  | FStar_Pervasives_Native.Some ch ->
    Hashing_Hash.check_all_hashes check_inplace_hashes_f load_hash ch out_dir (FStar_List.map (fun file -> (file, Options_Base.module_name file)) cmd_line_files)
    exit 0
  | FStar_Pervasives_Native.None ->
    exit 1
