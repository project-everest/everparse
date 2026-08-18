// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp
// See the 'F# Tutorial' project for more help.

module Wrapper

let everparse_version = Version.everparse_version

let everparse_filename =
  let suffix =
    if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux)
    then "Linux_x86_64.tar.gz"
    else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows)
    then "Windows_NT_x86_64.zip"
    else failwith "everparse_filename: Cannot determine OS platform"
  in
  "everparse_" ^ everparse_version ^ "_" ^ suffix

let everparse_url =
  "https://github.com/" ^ PackageHashes.everparse_repo ^ "/releases/download/" ^ everparse_version ^ "/" ^ everparse_filename

(* Update the hashes below when upgrading to a new binary package *)
let everparse_hash =
  if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux)
  then PackageHashes.linux_hash
  else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows)
  then PackageHashes.windows_hash
  else failwith "everparse_filename: Cannot determine OS platform"

let everparse_unpack dirname =
  if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux) then
    use f = System.IO.File.OpenRead(everparse_filename)
    use gz = new System.IO.Compression.GZipStream(f, System.IO.Compression.CompressionMode.Decompress)
    System.Formats.Tar.TarFile.ExtractToDirectory(gz, ".", false)
  else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows) then
    System.IO.Compression.ZipFile.ExtractToDirectory(everparse_filename, ".", false)
  else
    failwith "everparse_unpack: Cannot determine OS platform"
  System.Console.WriteLine("Waiting for 10 s")
  System.Threading.Thread.Sleep(10000)
  System.Console.WriteLine("Renaming directory")
  System.IO.Directory.Move("everparse", dirname)

let everparse_pkg_entrypoint dirname =
  if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Linux) then
    System.IO.Path.Combine(dirname, "everparse.sh")
  else if System.Runtime.InteropServices.RuntimeInformation.IsOSPlatform(System.Runtime.InteropServices.OSPlatform.Windows) then
    System.IO.Path.Combine(dirname, "everparse.cmd")
  else
    failwith "everparse_pkg_entrypoint: Cannot determine OS platform"

let hash_file filename =
    use h = System.Security.Cryptography.SHA256.Create ()
    use f = System.IO.File.OpenRead(filename)
    let a = h.ComputeHash(f)
    let sp = System.ReadOnlySpan(a, 0, a.Length)
    Hashing_Op.bytes_to_hex sp

[<EntryPoint>]
let main _ =
  let dirname =
    let everparse_home = System.Environment.GetEnvironmentVariable("EVERPARSE_HOME")
    if (everparse_home = null) then
       System.Console.WriteLine "EVERPARSE_HOME not defined"
       let dirname = "everparse-" ^ everparse_version
       if System.IO.Directory.Exists(dirname) then
         System.Console.WriteLine ("Using existing " ^ dirname ^ " subdirectory")
       else
         System.Console.WriteLine (dirname ^ " subdirectory not found")
         use wc = new System.Net.WebClient ()
         if System.IO.File.Exists(everparse_filename) then
           System.Console.WriteLine ("Found binary package " ^ everparse_filename)
         else
           System.Console.WriteLine ("Binary package not found. Downloading from " ^ everparse_url)
           System.Console.WriteLine "You are trying to call the EverParse/3d inplace hash checker with an unsupported EverParse/3d option. The only supported option is --check_inplace_hash . Do you want to try downloading a full EverParse binary package from GitHub Releases and running it? (y/N)" // please download and use a full EverParse binary package from https://github.com/project-everest/everparse/releases"
           if System.Convert.ToChar(System.Console.Read()).ToString() <> "y" then
             exit 1
           wc.DownloadFile(everparse_url, everparse_filename)
         let s = hash_file everparse_filename
         System.Console.WriteLine ("Expected hash: " ^ everparse_hash)
         System.Console.WriteLine ("Found hash: " ^ s)
         if s <> everparse_hash then
           System.Console.WriteLine ("Failed to download EverParse: hash mismatch")
           exit 1
         System.Console.WriteLine ("Unpacking " ^ everparse_filename)
         everparse_unpack dirname
       dirname
    else
      System.Console.WriteLine ("Using EverParse from EVERPARSE_HOME = " ^ everparse_home)
      everparse_home
  let argv = System.Environment.GetCommandLineArgs()
  let args = System.ArraySegment(argv, 1, argv.Length - 1)
  use p = System.Diagnostics.Process.Start(everparse_pkg_entrypoint dirname, args)
  p.WaitForExit ()
  p.ExitCode
