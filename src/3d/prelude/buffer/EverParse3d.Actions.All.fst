module EverParse3d.Actions.All
friend EverParse3d.Actions.Base
friend EverParse3d.InputStream.All
friend EverParse3d.InputStream.Buffer

let ___PUINT8 = LowStar.Buffer.buffer FStar.UInt8.t

let action_field_ptr
      #nz #wk (#k:Prelude.parser_kind nz wk) (#t:Type) (#p:Prelude.parser k t) (u:unit)
   = fun ctxt input startPosition ->
       let open LowParse.Slice in
       LowStar.Buffer.offset input.EverParse3d.InputStream.Buffer.Aux.buf (FStar.Int.Cast.uint64_to_uint32 startPosition)
