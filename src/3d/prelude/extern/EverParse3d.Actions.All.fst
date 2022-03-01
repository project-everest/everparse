module EverParse3d.Actions.All
friend EverParse3d.Actions.Base
friend EverParse3d.InputStream.All

let _ = EverParse3d.Actions.BackendFlagValue.backend_flag_value

let ___PUINT8 = LowStar.Buffer.buffer FStar.UInt8.t

let action_field_ptr u = false_elim ()

let action_field_ptr_after _ n =
  fun ctxt input _ currentPosition ->
  EverParse3d.InputStream.Extern.peep input currentPosition n

let action_field_pos_32 u = false_elim ()
