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

let everparse_version = "2023.01.23"

let everparse_url =
  let suffix =
    if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux)
    then "Linux_x86_64.tar.gz"
    else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows)
    then "Windows_NT_x86_64.zip"
    else failwith "everparse_url: Cannot determine OS platform"
  in
  "https://github.com/project-everest/everparse/releases/download/v" ^ everparse_version ^ "/everparse_v" ^ everparse_version ^ "_" ^ suffix

let everparse_filename =
  let suffix =
    if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux)
    then "tar.gz"
    else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows)
    then "zip"
    else failwith "everparse_filename: Cannot determine OS platform"
  in
  "everparse." ^ suffix

let everparse_hash =
  if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux)
  then "73826947643f3dedca20ba6c9aeeb4436b81e899ac9f85a07edf53a02933a408"
  else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows)
  then "17e578949cf98c752c5bc08fe81b573ef39f6b8ff340199b34697716f8b3ee6d"
  else failwith "everparse_filename: Cannot determine OS platform"

let everparse_unpack () =
  if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux) then
    use f = System.IO.File.OpenRead(everparse_filename)
    use gz = new System.IO.Compression.GZipStream(f, System.IO.Compression.CompressionMode.Decompress)
    System.Formats.Tar.TarFile.ExtractToDirectory(gz, ".", false)
  else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows) then
    System.IO.Compression.ZipFile.ExtractToDirectory(everparse_filename, ".", false)
  else
    failwith "everparse_unpack: Cannot determine OS platform"

let everparse_pkg_entrypoint dirname =
  if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux) then
    System.IO.Path.Combine(dirname, "everparse.sh")
  else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows) then
    System.IO.Path.Combine(dirname, "everparse.cmd")
  else
    failwith "everparse_pkg_entrypoint: Cannot determine OS platform"

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
         use wc = new System.Net.WebClient ()
         if System.IO.File.Exists(everparse_filename) then
           System.Console.WriteLine ("Found binary package " ^ everparse_filename)
         else
           System.Console.WriteLine ("Binary package not found. Downloading from " ^ everparse_url)
           wc.DownloadFile(everparse_url, everparse_filename)
         let s = hash_file everparse_filename
         System.Console.WriteLine ("Expected hash: " ^ everparse_hash)
         System.Console.WriteLine ("Found hash: " ^ s)
         if s <> everparse_hash then
           System.Console.WriteLine ("Failed to download EverParse: hash mismatch")
           exit 1
         System.Console.WriteLine ("Unpacking " ^ everparse_filename)
         everparse_unpack ()
       dirname
    else
      System.Console.WriteLine ("Using EverParse from EVERPARSE_HOME = " ^ everparse_home)
      everparse_home
  let argv = System.Environment.GetCommandLineArgs()
  let args = System.ArraySegment(argv, 1, argv.Length - 1)
  use p = System.Diagnostics.Process.Start(everparse_pkg_entrypoint dirname, args)
  p.WaitForExit ()
  p.ExitCode
