module LowParseExample5.Aux

module LPC = LowParse.Low.Combinators
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let parse_inner_raw =
  LPI.parse_u16 `LPC.nondep_then` LPI.parse_u16

let synth_inner (x: (U16.t * U16.t)) : Tot inner =
  let (left, right) = x in
  {left = left; right = right;}

let parse_inner' : LP.parser _ inner =
  parse_inner_raw `LPC.parse_synth` synth_inner

let parse_inner = parse_inner'

let synth_inner_recip (x: inner) : Tot (U16.t * U16.t) =
  (x.left, x.right)

let serialize_inner_raw : LP.serializer parse_inner_raw =
  LPC.serialize_nondep_then
    _
    LPI.serialize_u16
    ()
    _
    LPI.serialize_u16

let serialize_inner = LPC.serialize_synth _ synth_inner serialize_inner_raw synth_inner_recip ()

#set-options "--z3rlimit 16"

let serialize_inner_intro h b lo =
  LPC.valid_synth h parse_inner_raw synth_inner b lo;
  LPC.valid_nondep_then h LPI.parse_u16 LPI.parse_u16 b lo

#reset-options

let parse_t_raw =
  parse_inner ` LPC.nondep_then` LPI.parse_u32

let synth_t (x: (inner * U32.t)) : Tot t =
  let (inner, last) = x in
  {inner = inner; last = last;}

let parse_t' = parse_t_raw `LPC.parse_synth` synth_t

let parse_t_kind = LP.get_parser_kind parse_t'

let parse_t = parse_t'

let synth_t_recip (x: t) : Tot (inner * U32.t) =
  (x.inner, x.last)

let serialize_t_raw : LP.serializer parse_t_raw =
  LPC.serialize_nondep_then
    _
    serialize_inner
    ()
    _
    LPI.serialize_u32

let serialize_t = LPC.serialize_synth _ synth_t serialize_t_raw synth_t_recip ()

#set-options "--z3rlimit 32"

let serialize_t_intro h b lo =
  LPC.valid_synth h parse_t_raw synth_t b lo;
  LPC.valid_nondep_then h parse_inner LPI.parse_u32 b lo

#reset-options
