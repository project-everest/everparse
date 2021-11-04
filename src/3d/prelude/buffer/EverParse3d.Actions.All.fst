module EverParse3d.Actions.All
friend EverParse3d.Actions.Base
friend EverParse3d.InputStream.All
friend EverParse3d.InputStream.Buffer

let ___PUINT8 = LowStar.Buffer.buffer FStar.UInt8.t

let action_field_ptr
      #nz #wk (#k:Prelude.parser_kind nz wk) (#t:Type) (#p:Prelude.parser k t) (u:unit)
   = fun ctxt input startPosition ->
       let open LowParse.Slice in
       LowStar.Buffer.offset input.EverParse3d.InputStream.Buffer.Aux.buf (LowParse.Low.ErrorCode.uint64_to_uint32 startPosition)

let action_field_pos_32
      #nz #wk (#k:Prelude.parser_kind nz wk) (#t:Type) (#p:Prelude.parser k t) (u:unit)
   = fun ctxt input startPosition ->
       [@inline_let]
       let res = LowParse.Low.ErrorCode.uint64_to_uint32 startPosition in
       assert (FStar.UInt32.v res == FStar.UInt64.v startPosition); // sanity-check: no modulo here
       res
