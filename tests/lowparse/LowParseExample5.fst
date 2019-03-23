module LowParseExample5
include LowParseExample5.Aux

module LPC = LowParse.Spec.Combinators
module LPV = LowParse.Low.VLData
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

#set-options "--z3rlimit 16" //  --z3cliopt smt.arith.nl=false --z3cliopt smt.case_split=3"
// --using_facts_from '* -FStar.Kremlin.Endianness -LowParse.BigEndian -LowParse.BigEndianImpl.* -LowParse.Math -FStar.Math.*'"

let vltest () : HST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  HST.push_frame ();
  let b : LP.buffer8 = B.alloca 0uy 12ul in
  let sl = { LP.base = b; LP.len = 12ul; } in
  let j = LPI.write_u16 18us sl 2ul in
  let j = LPI.write_u16 42us sl j in
  let j = LPI.write_u32 1729ul sl j in
  let h = HST.get () in
  serialize_inner_intro h sl 2ul;
  serialize_t_intro h sl 2ul;
  let _ = LPV.finalize_bounded_vldata_strong 0 65535 serialize_t sl 0ul j in
  let h = HST.get () in
  assert (
    let v = ({ inner = ({ left = 18us; right = 42us; }); last = 1729ul;}) in
    LPV.parse_bounded_vldata_strong_pred 0 65535 serialize_t v /\
    LP.valid (LPV.parse_bounded_vldata_strong 0 65535 serialize_t) h sl 0ul /\
    LP.contents (LPV.parse_bounded_vldata_strong 0 65535 serialize_t) h sl 0ul == v
  );
  HST.pop_frame ()

let main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
   HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
=
  fun _ _ ->
  vltest ();
  C.EXIT_SUCCESS
