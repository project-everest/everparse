module Sample.Client
module Color = Sample.AutoGen_color
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Combinators
module L = FStar.List.Tot

(* A basic test: uses the auto-generated parsers and serializers
   to prove that parse . serialize = id *)
let simple_test (x:Color.color) : y:Color.color{y == x} =
  let bytes = Color.color_serializer32 x in
  match Color.color_parser32 bytes with
  | Some (x', n) ->
    assert (n  == 5ul);
    assert (x' == x);
    x'

(* Now, suppose we have our own types in bijection with the types
   auto-gen'd from the RFC

   The general idea is to derive parsers/serializers composed with the
   bijections to obtain mutually inverse parser/serializers for the new types.
*)

type rgb = {
  red:U8.t;
  green:U8.t;
  blue:U8.t;
}

type color' = {
  rgb:rgb;
  transparency:U16.t
}

let color_to_color' c =
  let rgb = {
    red = c.Color.red;
    green = c.Color.green;
    blue = c.Color.blue;
  } in
  { rgb = rgb;
    transparency = c.Color.transparency
  }

let color'_to_color c =
  { Color.red = c.rgb.red;
    Color.green = c.rgb.green;
    Color.blue = c.rgb.blue;
    Color.transparency = c.transparency
  }

let color'_parser : LP.parser _ color' =
  LP.parse_synth Color.color_parser color_to_color'

let color'_serializer : LP.serializer color'_parser =
  LP.serialize_synth _ color_to_color' Color.color_serializer color'_to_color ()

let color'_parser32 : LP.parser32 color'_parser =
  LP.parse32_synth Color.color_parser color_to_color' (fun x -> color_to_color' x) Color.color_parser32 ()

let color'_serializer32 : LP.serializer32 color'_serializer =
  LP.serialize32_synth _
     color_to_color'
     Color.color_serializer
     Color.color_serializer32
     color'_to_color
     (fun x -> color'_to_color x)
     ()

(* A basic test: uses the auto-generated parsers and serializers
   to prove that parse . serialize = id *)
let simple_test' (x:color') : y:color'{y == x} =
  let bytes = color'_serializer32 x in
  match color'_parser32 bytes with
  | Some (x', n) ->
    assert (n  == 5ul);
    assert (x' == x);
    x'
