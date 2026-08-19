module LowParseExample11

module LS = LowParse.SLow
module LL = LowParse.Low
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module L = FStar.List.Tot

let parse_t' = LL.parse_vclist 10 1000 LL.parse_bcvli LL.parse_bcvli

let kind_eq : squash (LL.get_parser_kind parse_t' == parse_t_kind) =
  _ by (FStar.Tactics.trefl ())

let type_eq : squash (t == LL.vlarray elem 10 1000) = _ by (FStar.Tactics.trefl ())

let parse_t = parse_t'

let serialize_t = LL.serialize_vclist 10 1000 LL.serialize_bcvli LL.serialize_bcvli

let parse32_t = LS.parse32_vclist 10ul 1000ul LS.parse32_bcvli LS.parse32_bcvli

let serialize32_t = 
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 10 1000 LL.parse_bcvli_kind LL.parse_bcvli_kind) in
  LS.serialize32_vclist 10 1000 LS.serialize32_bcvli LS.serialize32_bcvli

let size32_t = 
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 10 1000 LL.parse_bcvli_kind LL.parse_bcvli_kind) in
  LS.size32_vclist 10 1000 LS.size32_bcvli LS.size32_bcvli

let validate_t = LL.validate_vclist 10ul 1000ul LL.validate_bcvli LL.read_bcvli LL.validate_bcvli

let jump_t =  LL.jump_vclist 10 1000 LL.jump_bcvli LL.read_bcvli LL.jump_bcvli

#push-options "--z3rlimit 16"

let read_6th sl pos =
  let h = HST.get () in
  LL.valid_vclist_elim 10 1000 LL.parse_bcvli LL.parse_bcvli h sl pos;
  let len = LL.read_bcvli sl pos in
  let pos_payload = LL.jump_bcvli sl pos in
  let pos' = LL.jump_nlist len (LL.jump_bcvli <: LL.jumper LL.parse_bcvli) sl pos_payload in
  LL.valid_nlist_valid_list (U32.v len) LL.parse_bcvli h sl pos_payload;
  let pos_6th = LL.list_nth LL.parse_bcvli LL.jump_bcvli sl pos_payload pos' 6ul in
  LL.read_bcvli sl pos_6th

#pop-options

let main _ _ = C.EXIT_SUCCESS
