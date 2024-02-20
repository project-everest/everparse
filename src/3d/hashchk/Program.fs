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

let hash_file filename =
    use h = System.Security.Cryptography.SHA256.Create ()
    use f = System.IO.File.OpenRead(filename)
    let a = h.ComputeHash(f)
    let sp = System.ReadOnlySpan(a, 0, a.Length)
    Hashing_Op.bytes_to_hex sp

[<EntryPoint>]
let main _ =
  (* Parse command-line options. This action is only accumulating values into globals, without any further action (other than --help and --version, which interrupt the execution.) *)
  let _ = Options.parse_cmd_line() in
  (* Special mode: --check_inplace_hashes *)
  let inplace_hashes = Options.check_inplace_hashes () in
  if not (List.isEmpty inplace_hashes)
  then
    Hashing_Hash.check_inplace_hashes check_inplace_hashes_f inplace_hashes
    exit 0
  System.Console.WriteLine "You are trying to call the EverParse/3d inplace hash checker with an unsupported EverParse/3d option. The only supported option is --check_inplace_hash . Do you want to try downloading a full EverParse binary package from GitHub Releases and running it? (y/N)" // please download and use a full EverParse binary package from https://github.com/project-everest/everparse/releases"
  if System.Console.ReadKey().KeyChar.ToString() <> "y" then
     exit 1
  let dirname =
    let everparse_home = System.Environment.GetEnvironmentVariable("EVERPARSE_HOME")
    if (everparse_home = null) then
       System.Console.WriteLine "EVERPARSE_HOME not defined"
       let dirname = "everparse"
       if System.IO.Directory.Exists(dirname) then
         System.Console.WriteLine ("Using existing " ^ dirname ^ " subdirectory")
       else
         System.Console.WriteLine (dirname ^ " subdirectory not found")
         let url = "https://github.com/project-everest/everparse/releases/download/v2023.01.23/everparse_v2023.01.23_Linux_x86_64.tar.gz"
         let filename = "everparse.tar.gz"
         use wc = new System.Net.WebClient ()
         if System.IO.File.Exists(filename) then
           System.Console.WriteLine ("Found binary package " ^ filename)
         else
           System.Console.WriteLine ("Binary package not found. Downloading from " ^ url)
           wc.DownloadFile(url, filename)
         let hash = "73826947643f3dedca20ba6c9aeeb4436b81e899ac9f85a07edf53a02933a408"
         let s = hash_file filename
         System.Console.WriteLine ("Expected hash: " ^ hash)
         System.Console.WriteLine ("Found hash: " ^ s)
         if s <> hash then
           System.Console.WriteLine ("Failed to download EverParse: hash mismatch")
           exit 1
         System.Console.WriteLine ("Unpacking " ^ filename)
         use f = System.IO.File.OpenRead(filename)
         use gz = new System.IO.Compression.GZipStream(f, System.IO.Compression.CompressionMode.Decompress)
         System.Formats.Tar.TarFile.ExtractToDirectory(gz, ".", false)
       dirname
    else
      System.Console.WriteLine ("Using EverParse from EVERPARSE_HOME = " ^ everparse_home)
      everparse_home
  let argv = System.Environment.GetCommandLineArgs()
  let args = System.ArraySegment(argv, 1, argv.Length - 1)
  use p = System.Diagnostics.Process.Start(dirname ^ "/everparse.sh", args)
  p.WaitForExit ()
  p.ExitCode
