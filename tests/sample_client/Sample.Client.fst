module Sample.Client
module Color = Sample.AutoGen_color
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

let simple_test (x:Color.color) : y:Color.color{y == x} =
  let bytes = Color.color_serializer32 x in
  match Color.color_parser32 bytes with
  | Some (x', n) ->
    assert (n  == 5ul);
    assert (x' == x);
    x'
