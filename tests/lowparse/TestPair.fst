module TestPair
module P = Pair
module U8 = FStar.UInt8
module FB = LowStar.PrefixFreezableBuffer
module LM = LowParseExampleMono
module LMI = LowParse.MLow.Int

assume val buf :
  s: LM.slice{
    FB.recallable s.LM.base
  }
let irepr #t #k (p:LM.parser k t) = LM.irepr p buf

module LPI = LowParse.Spec.AllIntegers

open FStar.HyperStack.ST
assume val havoc : unit -> Stack unit (fun h -> True) (fun _ _ _ -> True)

let read_components (i:irepr P.pair_parser)
  : Stack (UInt32.t * UInt32.t)
    (requires fun h ->
      True)
    (ensures fun h0 x h1 ->
      True)
  = LM.recall_valid i;
    let x = P.accessor_pair_fst buf (LM.irepr_pos i) in
    havoc();
    LM.recall_valid i;
    let y : UInt32.t = P.accessor_pair_snd buf (LM.irepr_pos i) in
    x, y

module B = LowStar.Buffer

let read_components2 (i:irepr P.pair_parser)
  : Stack (x: (irepr LPI.parse_u32 * irepr LPI.parse_u16) { LM.irepr_v i == {P.fst = LM.irepr_v (fst x); P.snd = LM.irepr_v (snd x)} } )
    (requires fun h ->
      True)
    (ensures fun h0 x h1 ->
      True)
  = LM.recall_valid i;
    let x = P.accessor_pair_fst buf (LM.irepr_pos i) in
    FB.recall_frozen_until_default buf.LM.base;
    let x : irepr LPI.parse_u32 = LM.witness_valid buf x in

    havoc();

    LM.recall_valid i;
    let y : UInt32.t = P.accessor_pair_snd buf (LM.irepr_pos i) in
    FB.recall_frozen_until_default buf.LM.base;
    assert (UInt32.v y >= 4);
    let y : irepr LPI.parse_u16 = LM.witness_valid buf y in
    x, y

let read_components3 (i:irepr P.pair_parser)
  : Stack (x: (irepr LPI.parse_u32 * irepr LPI.parse_u16) { LM.irepr_v i == {P.fst = LM.irepr_v (fst x); P.snd = LM.irepr_v (snd x)} } )
    (requires fun h ->
      True)
    (ensures fun h0 x h1 ->
      True)
= let xfst = LM.iaccess P.accessor_pair_fst i in
  havoc();
  let xsnd = LM.iaccess P.accessor_pair_snd i in
  (xfst, xsnd)

module HS = FStar.HyperStack
module U32 = FStar.UInt32

let frozen_until = LM.buffer_frozen_until buf.LM.base

let iwrite_u16 (u:UInt16.t) (p:UInt32.t)
  : Stack (irepr LPI.parse_u16)
    (requires fun h ->
      frozen_until h <= U32.v p /\
      U32.v p + 2 < U32.v buf.LM.len)
    (ensures fun h0 i h1 ->
      LM.irepr_pos i == p /\
      LM.irepr_pos' i == U32.(p +^ 2ul) /\
      LM.irepr_v i == u   /\
      frozen_until h1 == U32.v p + 2 /\
      B.modifies (B.loc_buffer buf.LM.base) h0 h1)
   = FB.recall_frozen_until_default buf.LM.base;
     B.recall buf.LM.base;
     let h0 = get () in
     let p' = LMI.write_u16 u buf p in
     let h1 = get () in
     let p' = p `U32.add` 2ul in
     B.modifies_buffer_from_to_elim buf.LM.base 0ul 4ul (LM.loc_slice_from_to buf p p') h0 h1;
     FB.recall_frozen_until_default buf.LM.base;
     FB.freeze buf.LM.base p' ;
     let h2 = get () in
     LM.valid_exact_ext_intro LPI.parse_u16 h1 buf p p' h2 buf p p' ;
     LM.witness_valid buf p


let iwrite_u32 (u:UInt32.t) (p:UInt32.t)
  : Stack (irepr LPI.parse_u32)
    (requires fun h ->
      frozen_until h <= U32.v p /\
      U32.v p + 4 < U32.v buf.LM.len)
    (ensures fun h0 i h1 ->
      LM.irepr_pos i == p /\
      LM.irepr_pos' i == U32.(p +^ 4ul) /\
      LM.irepr_v i == u   /\
      frozen_until h1 == U32.v p + 4 /\
      B.modifies (B.loc_buffer buf.LM.base) h0 h1)
   = FB.recall_frozen_until_default buf.LM.base;
     B.recall buf.LM.base;
     let h0 = get () in
     let p' = LMI.write_u32 u buf p in
     let h1 = get () in
     let p' = p `U32.add` 4ul in
     B.modifies_buffer_from_to_elim buf.LM.base 0ul 4ul (LM.loc_slice_from_to buf p p') h0 h1;
     FB.recall_frozen_until_default buf.LM.base;
     FB.freeze buf.LM.base p' ;
     let h2 = get () in
     LM.valid_exact_ext_intro LPI.parse_u32 h1 buf p p' h2 buf p p' ;
     LM.witness_valid buf p

assume val havoc_l :
  l:B.loc -> Stack unit (fun h -> True) (fun h0 _ h1 ->
  B.modifies l h0 h1 /\
  frozen_until h0 == frozen_until h1)

assume val some_loc: B.loc

let iwrite_pair (u0:UInt32.t) (u1:UInt16.t) (p:UInt32.t)
  : Stack (irepr P.pair_parser)
    (requires fun h ->
      frozen_until h <= U32.v p /\
      U32.v p + 6 < U32.v buf.LM.len)
    (ensures fun h0 i h1 ->
      LM.irepr_pos i == p /\
      LM.irepr_pos' i == U32.(p +^ 6ul) /\
      LM.irepr_v i == P.({fst=u0; snd=u1})  /\
      frozen_until h1 == U32.v p + 6 /\
      B.modifies (B.loc_union some_loc (B.loc_buffer buf.LM.base)) h0 h1)
   = let i0 = iwrite_u32 u0 p in
     havoc_l some_loc;
     let i1 = iwrite_u16 u1 U32.(p +^ 4ul) in
     let h = get () in
     LM.recall_valid i0;
     LM.recall_valid i1;
     Pair.pair_valid h buf p;
     LM.witness_valid buf p

(* with the iwrite wrapper *)

let iwrite_pair1 (u0:UInt32.t) (u1:UInt16.t) (p:UInt32.t)
  : Stack (irepr P.pair_parser)
    (requires fun h ->
      frozen_until h <= U32.v p /\
      U32.v p + 6 < U32.v buf.LM.len)
    (ensures fun h0 i h1 ->
      LM.irepr_pos i == p /\
      LM.irepr_pos' i == U32.(p +^ 6ul) /\
      LM.irepr_v i == P.({fst=u0; snd=u1})  /\
      frozen_until h1 == U32.v p + 6 /\
      B.modifies (B.loc_union some_loc (B.loc_buffer buf.LM.base)) h0 h1)
   = let i0 = LM.iwrite LMI.write_u32 u0 buf p in
     havoc_l some_loc;
     let i1 = LM.iwrite LMI.write_u16 u1 buf U32.(p +^ 4ul) in
     let h = get () in
     LM.recall_valid i0;
     LM.recall_valid i1;
     Pair.pair_valid h buf p;
     LM.witness_valid buf p

(* with only one freeze, thanks to frozen_until_frame that preserves the value of the length header across LowParse writers *)

let iwrite_pair2 (u0:UInt32.t) (u1:UInt16.t) (p:UInt32.t)
  : Stack (irepr P.pair_parser)
    (requires fun h ->
      frozen_until h <= U32.v p /\
      U32.v p + 6 < U32.v buf.LM.len)
    (ensures fun h0 i h1 ->
      LM.irepr_pos i == p /\
      LM.irepr_pos' i == U32.(p +^ 6ul) /\
      LM.irepr_v i == P.({fst=u0; snd=u1})  /\
      frozen_until h1 == U32.v p + 6 /\
      B.modifies (B.loc_union some_loc (B.loc_buffer buf.LM.base)) h0 h1)
= FB.recall_frozen_until_default buf.LM.base; // for writable
  B.recall buf.LM.base; // for live
  let p1 = LMI.write_u32 u0 buf p in
  let p2 = LMI.write_u16 u1 buf p1 in
  let h = get () in
  Pair.pair_valid h buf p;
  LM.freeze_valid Pair.pair_parser buf p p2
