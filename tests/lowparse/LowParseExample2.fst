module LowParseExample2

open FStar.HyperStack.ST
module B32 = FStar.Bytes
module U32 = FStar.UInt32
module LP = LowParse.SLow
module TESTLIB = LowParse.TestLib.SLow

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction
let synth_t
  (x: LP.parse_bounded_vlbytes_t 0 65535)
: Tot t
= { b = x }

let synth_t_inj
  ()
: Lemma
  (LP.synth_injective synth_t)
= ()

let parse_t_spec : LP.parser _ t =
  synth_t_inj ();
  LP.parse_bounded_vlbytes 0 65535 `LP.parse_synth` synth_t
  
inline_for_extraction
let parse_t_impl : LP.parser32 parse_t_spec =
  [@inline_let]
  let _ = synth_t_inj () in
  LP.parse32_synth
    _
    synth_t
    (fun x -> synth_t x)
    (LP.parse32_bounded_vlbytes 0 0ul 65535 65535ul)
    ()

inline_for_extraction
let synth_t_recip
  (x: t)
: Tot (LP.parse_bounded_vlbytes_t 0 65535)
= x.b

let synth_t_recip_inv
  ()
: Lemma
  (LP.synth_inverse synth_t synth_t_recip)
= ()

let serialize_t_spec : LP.serializer parse_t_spec =
  synth_t_inj ();
  synth_t_recip_inv ();
  LP.serialize_synth
    _
    synth_t
    (LP.serialize_bounded_vlbytes 0 65535)
    synth_t_recip
    ()

inline_for_extraction
let serialize_t_impl : LP.serializer32 serialize_t_spec =
  [@inline_let]
  let _ = synth_t_inj () in
  [@inline_let]
  let _ = synth_t_recip_inv () in
  LP.serialize32_synth
    _
    synth_t
    _
    (LP.serialize32_bounded_vlbytes 0 65535)
    synth_t_recip
    (fun x -> synth_t_recip x)
    ()

inline_for_extraction
let size32_t : LP.size32 serialize_t_spec =
  [@inline_let]
  let _ = synth_t_inj () in
  [@inline_let]
  let _ = synth_t_recip_inv () in
  LP.size32_synth
    _
    synth_t
    _
    (LP.size32_bounded_vlbytes 0 65535)
    synth_t_recip
    (fun x -> synth_t_recip x)
    ()

let t'_l_serializable x =
  LP.parse_bounded_vldata_strong_pred 0 255 (LP.serialize_list _ serialize_t_spec) x

let check_t'_l_serializable x =
  LP.check_vldata_payload_size32 0 0ul 255 255ul (LP.size32_list size32_t ()) x

inline_for_extraction
let synth_t'
  (x: LP.parse_bounded_vldata_strong_t 0 255 (LP.serialize_list _ serialize_t_spec))
: Tot t'
= { l = x }

let synth_t'_inj () : Lemma
  (LP.synth_injective synth_t')
= ()

let parse_t'_spec : LP.parser _ t' =
  synth_t'_inj ();
  LP.parse_bounded_vldata_strong 0 255 (LP.serialize_list _ serialize_t_spec)
  `LP.parse_synth`
  synth_t'

inline_for_extraction
let parse_t'_impl : LP.parser32 parse_t'_spec =
  [@inline_let]
  let _ = synth_t'_inj () in
  LP.parse32_synth
    _
    synth_t'
    (fun x -> synth_t' x)
    (LP.parse32_bounded_vldata_strong 
      0 0ul 255 255ul
      (LP.serialize_list _ serialize_t_spec)
      (LP.parse32_list parse_t_impl)
    )
    ()

let parse_t' x = parse_t'_impl x

inline_for_extraction
let synth_t'_recip
  (x: t')
: Tot (LP.parse_bounded_vldata_strong_t 0 255 (LP.serialize_list _ serialize_t_spec))
= x.l

let synth_t'_recip_inv () : Lemma
  (LP.synth_inverse synth_t' synth_t'_recip)
= ()

let serialize_t'_spec : LP.serializer parse_t'_spec =
  synth_t'_inj ();
  synth_t'_recip_inv ();
  LP.serialize_synth
    _
    synth_t'
    (LP.serialize_bounded_vldata_strong 0 255 (LP.serialize_list _ serialize_t_spec))
    synth_t'_recip
    ()

inline_for_extraction
let serialize_t'_impl : LP.serializer32 serialize_t'_spec =
  [@inline_let]
  let _ = synth_t'_inj () in
  [@inline_let]
  let _ = synth_t'_recip_inv () in
  LP.serialize32_synth
    _
    synth_t'
    _
    (LP.serialize32_bounded_vldata_strong 0 255 (LP.partial_serialize32_list _ _ serialize_t_impl ()))
    synth_t'_recip
    (fun x -> synth_t'_recip x)
    ()

let serialize_t' x = serialize_t'_impl x

let serialize_then_parse_t' x =
  LP.serializer32_then_parser32 _ parse_t'_impl serialize_t'_impl x

let parse_then_serialize_t' x y consumed =
  LP.parser32_then_serializer32 _ parse_t'_impl serialize_t'_impl x

#reset-options "--using_facts_from '* -LowParse'"

// BUGBUG: HACK for Kremlin kremlib issue
// Dummy function, to call some FStar.Bytes functions.  This
// causes Kremlin to emit type declarations that are needed bytes
// krembytes.h.
let dummy (_:unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  assume false;
  push_frame();
  let p = FStar.Bytes.twobytes (0uy, 1uy) in
  let p = FStar.Bytes.split p 1ul in
  let p = FStar.Bytes.iutf8_opt (FStar.Bytes.utf8_encode "Napoléon") in
  pop_frame()

let main argc argv =
  push_frame ();
  dummy();
  pop_frame ();
  C.EXIT_SUCCESS
