module Pair

open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module LPI = LowParse.Spec.AllIntegers
module LL = LowParse.MLow.Base
module L = FStar.List.Tot
module B = LowStar.Buffer
module BY = FStar.Bytes
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST


type pair = {
  fst : U32.t;
  snd : U16.t;
}

inline_for_extraction noextract let pair_parser_kind = LP.strong_parser_kind 6 6 (Some LP.ParserKindMetadataTotal)

noextract val pair_parser: LP.parser pair_parser_kind pair

noextract val pair_serializer: LP.serializer pair_parser

noextract val pair_bytesize (x:pair) : GTot nat

noextract val pair_bytesize_eq (x:pair) : Lemma (pair_bytesize x == Seq.length (LP.serialize pair_serializer x))

val pair_parser32: LP.parser32 pair_parser

val pair_serializer32: LP.serializer32 pair_serializer

val pair_size32: LP.size32 pair_serializer

let pair_validator: LL.validator pair_parser = LL.validate_total_constant_size pair_parser 6ul ()

let pair_jumper: LL.jumper pair_parser = LL.jump_constant_size pair_parser 6ul ()

val pair_bytesize_eqn (x: pair) : Lemma (pair_bytesize x == 4 + 2) [SMTPat (pair_bytesize x)]

noextract let clens_pair_fst : LL.clens pair U32.t = {
  LL.clens_cond = (fun _ -> True);
  LL.clens_get = (fun x -> x.fst);
}

noextract let clens_pair_snd : LL.clens pair U16.t = {
  LL.clens_cond = (fun _ -> True);
  LL.clens_get = (fun x -> x.snd);
}

val gaccessor_pair_fst : LL.gaccessor pair_parser LPI.parse_u32 clens_pair_fst

inline_for_extraction val accessor_pair_fst : LL.accessor gaccessor_pair_fst

val gaccessor_pair_snd : LL.gaccessor pair_parser LPI.parse_u16 clens_pair_snd

inline_for_extraction val accessor_pair_snd : LL.accessor gaccessor_pair_snd

val pair_valid (#r #s:_) (h:HS.mem) (input:LL.slice r s) (pos0:U32.t) : Lemma
  (requires
    LL.valid LPI.parse_u32 h input pos0 /\ (
    let pos1 = LL.get_valid_pos LPI.parse_u32 h input pos0 in
    LL.valid LPI.parse_u16 h input pos1)
  )
  (ensures (
    let pos1 = LL.get_valid_pos LPI.parse_u32 h input pos0 in
    let pos2 = LL.get_valid_pos LPI.parse_u16 h input pos1 in
    LL.valid_content_pos pair_parser h input pos0
      ({
        fst = LL.contents LPI.parse_u32 h input pos0;
        snd = LL.contents LPI.parse_u16 h input pos1;
      }) pos2
  ))

