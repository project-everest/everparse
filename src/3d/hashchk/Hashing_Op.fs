module Hashing_Op

type byte_array(ap: System.Buffers.ArrayPool<byte>, len: int32) =
    let ar : byte[] = ap.Rent(len)
    member val array = ar
    interface System.IDisposable with
      member this.Dispose() = ap.Return(ar, false)

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
    interface System.IDisposable with
      member this.Dispose() =
        h.Dispose()

let hash_bool (h: hash_state) (b: bool) : unit =
    let byte : byte = System.Convert.ToByte (if b then 1 else 0)
    use arr = h.new_array(1)
    arr.array[0] <- byte
    h.AppendData arr

let hash_int (h: hash_state) (i: int32) : unit =
    use arr = h.new_array(4)
    System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian (arr.array, i)
    h.AppendData arr

let hash_file (h: hash_state) (f: string) : unit =
    use file = System.IO.File.Open(f, System.IO.FileMode.Open, System.IO.FileAccess.Read)
    let len = int32 file.Length
    hash_int h len
    use arr = h.new_array(len)
    let read = file.Read(arr.array, 0, len)
    assert (read = len)
    h.AppendData arr

let hash_file_option (h: hash_state) (s: Option<string>) : unit =
    match s with
    | None -> hash_bool h false
    | Some f -> hash_bool h true; hash_file h f

let hash_string (h: hash_state) (s: string) : unit =
    let len = int32 (h.encoding.GetByteCount(s))
    hash_int h len
    use arr = h.new_array(len)
    let encoded = h.encoding.GetBytes(s, 0, s.Length, arr.array, 0)
    assert (encoded = len)
    h.AppendData arr
