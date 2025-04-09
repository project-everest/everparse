module CDDL.Pulse.Attr
module U32 = FStar.UInt32

irreducible let bundle_get_impl_type_attr : unit = ()

irreducible let bundle_attr : unit = ()

[@@bundle_attr]
let filter_char (c: FStar.Char.char) : Tot bool =
  let code = FStar.Char.u32_of_char c in
  (code `U32.gte` FStar.Char.u32_of_char 'A' &&
    code `U32.lte` FStar.Char.u32_of_char 'Z') ||
  (code `U32.gte` FStar.Char.u32_of_char 'a' &&
    code `U32.lte` FStar.Char.u32_of_char 'z') ||
  (code `U32.gte` FStar.Char.u32_of_char '0' &&
    code `U32.lte` FStar.Char.u32_of_char '9') ||
  code = FStar.Char.u32_of_char '_'

[@@bundle_attr]
let filter_name (name: string) = 
  FStar.String.string_of_list (List.Tot.filter filter_char (FStar.String.list_of_string name))
