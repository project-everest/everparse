module Hashing_Op

type byte_array(ap: System.Buffers.ArrayPool<byte>, len: int32) =
    let ar : byte[] = ap.Rent(len)
    member val array = ar
    interface System.IDisposable with
      member this.Dispose() = ap.Return(ar, false)

let hex_digits = [| "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "a"; "b"; "c"; "d"; "e"; "f" |]

let byte_to_hex (b: byte) =
    System.String.Concat (hex_digits.[int b / 16], hex_digits.[int b % 16])

let rec bytes_to_hex0 (b: byte[]) (i: int) : string =
    if i <= 0
    then ""
    else
        let j = i - 1
        System.String.Concat (bytes_to_hex0 b j, byte_to_hex b.[j])

let bytes_to_hex (b: byte[]) : string =
    bytes_to_hex0 b b.Length

type hash_state() =
    let enc = new System.Text.UTF8Encoding(false, true)
    let ap = System.Buffers.ArrayPool.Create ()
    let h : System.Security.Cryptography.IncrementalHash =
        System.Security.Cryptography.IncrementalHash.CreateHash(System.Security.Cryptography.HashAlgorithmName.SHA256)
    member this.encoding = enc
    member this.AppendData(ar: byte_array) =
        h.AppendData(ar.array)
    member this.new_array(len: int32) : byte_array =
        new byte_array(ap, len)
    member this.finish() : string =
        let len = h.HashLengthInBytes
        use arr = this.new_array(len)
        let dest = System.Span(arr.array)
        ignore (h.GetHashAndReset(dest))
        bytes_to_hex arr.array
    interface System.IDisposable with
      member this.Dispose() =
        h.Dispose()

let hash_init () : hash_state =
    new hash_state ()

let hash_bool (h: hash_state) (b: bool) : unit =
    let byte : byte = System.Convert.ToByte (if b then 1 else 0)
    use arr = h.new_array(1)
    arr.array.[0] <- byte
    h.AppendData arr

let hash_int (h: hash_state) (i: int32) : unit =
    use arr = h.new_array(4)
    let sp = System.Span(arr.array)
    System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian (sp, i)
    h.AppendData arr

let hash_file (h: hash_state) (f: string) : unit =
    use file = System.IO.File.Open(f, System.IO.FileMode.Open, System.IO.FileAccess.Read)
    let len = int32 file.Length
    hash_int h len
    use arr = h.new_array(len)
    let read = file.Read(arr.array, 0, len)
    assert (read = len)
    h.AppendData arr

let hash_file_option (h: hash_state) (s: FStar_Pervasives_Native.option<string>) : unit =
    match s with
    | FStar_Pervasives_Native.None -> hash_bool h false
    | FStar_Pervasives_Native.Some f -> hash_bool h true; hash_file h f

let hash_string (h: hash_state) (s: string) : unit =
    let len = int32 (h.encoding.GetByteCount(s))
    hash_int h len
    use arr = h.new_array(len)
    let encoded = h.encoding.GetBytes(s, 0, s.Length, arr.array, 0)
    assert (encoded = len)
    h.AppendData arr

let hash_finish (h: hash_state) : string =
    h.finish()
