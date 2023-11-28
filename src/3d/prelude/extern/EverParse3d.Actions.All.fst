module EverParse3d.Actions.All
friend EverParse3d.Actions.Base
friend EverParse3d.InputStream.All

let _ = EverParse3d.Actions.BackendFlagValue.backend_flag_value

let ___PUINT8 = (b:LowStar.Buffer.buffer FStar.UInt8.t { ~ (LowStar.Buffer.g_is_null b) })

let action_field_ptr u = false_elim ()

let action_field_ptr_after _ n write_to =
  fun ctxt _err input _len _posBefore currentPosition ->
  let buf = EverParse3d.InputStream.Extern.peep input currentPosition n in
  let buf_not_null = not (LowStar.Buffer.is_null buf) in
  if buf_not_null
  then begin
    let open LowStar.BufferOps in
    write_to *= buf
  end;
  buf_not_null

let action_field_ptr_after_with_setter _ n write_to =
  fun ctxt _err input _len _posBefore currentPosition ->
  let buf = EverParse3d.InputStream.Extern.peep input currentPosition n in
  let buf_not_null = not (LowStar.Buffer.is_null buf) in
  if buf_not_null
  then
    write_to buf ()
  ;
  buf_not_null

let action_field_pos_32 u = false_elim ()
