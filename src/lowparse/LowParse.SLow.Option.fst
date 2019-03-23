module LowParse.SLow.Option
include LowParse.Spec.Option
include LowParse.SLow.Base

module U32 = FStar.UInt32
module B32 = FStar.Bytes

inline_for_extraction
let parse32_option (#k: parser_kind) (#t: Type) (#p: parser k t) (p32: parser32 p) : Tot (parser32 (parse_option p)) =
  fun input -> ((match p32 input with
  | Some (x, consumed) -> Some (Some x, consumed)
  | _ -> Some (None, 0ul)) <: (y: option (option t * U32.t) { parser32_correct (parse_option p) input y } ))

inline_for_extraction
let serialize32_option (#k: parser_kind) (#t: Type) (#p: parser k t) (#s: serializer p) (s32: serializer32 s) (u: squash (k.parser_kind_low > 0)) : Tot (serializer32 (serialize_option s u)) =
  fun input -> ((match input with
  | None ->
    [@inline_let]
    let res = B32.empty_bytes in
    assert (B32.reveal res `Seq.equal` Seq.empty);
    res
  | Some y -> s32 y) <: (y: B32.bytes { serializer32_correct (serialize_option s u) input y } ))

inline_for_extraction
let size32_option (#k: parser_kind) (#t: Type) (#p: parser k t) (#s: serializer p) (s32: size32 s) (u: squash (k.parser_kind_low > 0)) : Tot (size32 (serialize_option s u)) =
  fun input -> ((match input with
  | None -> 0ul
  | Some y -> s32 y) <: (y: U32.t { size32_postcond (serialize_option s u) input y } ))
