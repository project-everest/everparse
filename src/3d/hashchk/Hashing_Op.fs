module Hashing_Op

let debug_hash = false

type byte_array(ap: System.Buffers.ArrayPool<byte>, len: int32) =
    let ar : byte[] = ap.Rent(len)
    member this.rw = System.Span(ar, 0, len)
    member this.ro = System.ReadOnlySpan(ar, 0, len)
    interface System.IDisposable with
      member this.Dispose() = ap.Return(ar, false)

let hex_digits = [| "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "a"; "b"; "c"; "d"; "e"; "f" |]

let byte_to_hex (b: byte) =
    System.String.Concat (hex_digits.[int b / 16], hex_digits.[int b % 16])

let rec bytes_to_hex0 (b: System.ReadOnlySpan<byte>) (i: int) : string =
    if i <= 0
    then ""
    else
        let j = i - 1
        System.String.Concat (bytes_to_hex0 b j, byte_to_hex b.[j])

let bytes_to_hex (b: System.ReadOnlySpan<byte>) : string =
    bytes_to_hex0 b b.Length

type hash_state() =
    let enc = new System.Text.UTF8Encoding(false, true)
    let ap = System.Buffers.ArrayPool.Create ()
    let h : System.Security.Cryptography.IncrementalHash =
        System.Security.Cryptography.IncrementalHash.CreateHash(System.Security.Cryptography.HashAlgorithmName.SHA256)
    member this.encoding = enc
    member this.AppendData(ar: byte_array) =
        if debug_hash then begin
          let s = bytes_to_hex ar.ro
          System.Console.WriteLine ("Trying to update with: " ^ s)
        end
        h.AppendData(ar.ro)
        if debug_hash then begin
          let len = h.HashLengthInBytes
          use arr = this.new_array(len)
          ignore (h.GetCurrentHash(arr.rw))
          let s = bytes_to_hex arr.ro
          System.Console.WriteLine ("Update: " ^ s)
        end
    member this.new_array(len: int32) : byte_array =
        new byte_array(ap, len)
    member this.finish() : string =
        let len = h.HashLengthInBytes
        use arr = this.new_array(len)
        ignore (h.GetHashAndReset(arr.rw))
        bytes_to_hex arr.ro
    interface System.IDisposable with
      member this.Dispose() =
        h.Dispose()

let hash_init () : hash_state =
    new hash_state ()

let hash_bool (h: hash_state) (b: bool) : unit =
    let byte : byte = System.Convert.ToByte (if b then 1 else 0)
    use arr = h.new_array(1)
    arr.rw.[0] <- byte
    h.AppendData arr

let hash_int (h: hash_state) (i: int32) : unit =
    use arr = h.new_array(4)
    System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian (arr.rw, i)
    h.AppendData arr

let hash_file (h: hash_state) (f: string) : unit =
    use file = System.IO.File.Open(f, System.IO.FileMode.Open, System.IO.FileAccess.Read)
    let len = int32 file.Length
    hash_int h len
    use arr = h.new_array(len)
    let read = file.Read(arr.rw)
    assert (read = len)
    h.AppendData arr

let hash_file_option (h: hash_state) (s: FStar_Pervasives_Native.option<string>) : unit =
    match s with
    | FStar_Pervasives_Native.None -> hash_bool h false
    | FStar_Pervasives_Native.Some f -> hash_bool h true; hash_file h f

let hash_string (h: hash_state) (s: string) : unit =
    if debug_hash then begin
      System.Console.WriteLine("hash_string: \"" ^ s ^ "\"")
    end
    let len = int32 (h.encoding.GetByteCount(s))
    hash_int h len
    use arr = h.new_array(len)
    let encoded = h.encoding.GetBytes(System.String.op_Implicit(s), arr.rw)
    assert (encoded = len)
    h.AppendData arr

let hash_finish (h: hash_state) : string =
    h.finish()
