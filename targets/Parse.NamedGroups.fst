module Parse.NamedGroups

open Parse.Lemmas
open Parse.NamedGroup

module LP = LowParse.SLow
module L = FStar.List.Tot


(* Types *) 

(* https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.7

    struct {
        NamedGroup named_group_list<2..2^16-1>;
    } NamedGroupList;
           
*)

type named_groups = l:list named_group {1 <= L.length l && L.length l <= 32767}

private
let bytesize (gs:named_groups) = 2 + (op_Multiply named_group_bytesize (L.length gs))

private
let nglist_serializer = LP.serialize_list _ named_group_serializer


inline_for_extraction
let synth_named_groups
  (l:LP.parse_bounded_vldata_strong_t 2 65535 nglist_serializer)
  : Tot (l:named_groups)
  = [@inline_let]
    let l' : list named_group = l in
    [@inline_let]
    let _ = assume (1 <= L.length l' /\ L.length l' <= 32767) in
    l'

inline_for_extraction
let synth_named_groups_recip
  (l:named_groups)
  : Tot (l:LP.parse_bounded_vldata_strong_t 2 65535 nglist_serializer)
  = [@inline_let]
    let l' : list named_group = l in
    [@inline_let]
    let _ = assume (LP.parse_bounded_vldata_strong_pred 2 65535 nglist_serializer l') in
    l'

(* Parsers *)

let named_groups_parser_kind = LP.parse_bounded_vldata_kind 2 65535

let named_groups_parser: LP.parser named_groups_parser_kind _ =
  LP.parse_synth
    (LP.parse_bounded_vldata_strong 2 65535 nglist_serializer)
    synth_named_groups

inline_for_extraction
let named_groups_parser32: LP.parser32 named_groups_parser =
  LP.parse32_synth
    _
    synth_named_groups
    (fun x -> synth_named_groups x)
    (LP.parse32_bounded_vldata_strong 2 2ul 65535 65535ul nglist_serializer (LP.parse32_list named_group_parser32))
    ()


(* Serialization *) 

let named_groups_serializer: LP.serializer named_groups_parser =
  LP.serialize_synth
    _
    synth_named_groups
    (LP.serialize_bounded_vldata_strong 2 65535 (LP.serialize_list named_group_parser named_group_serializer))
    synth_named_groups_recip
    ()

inline_for_extraction
let named_groups_serializer32: LP.serializer32 named_groups_serializer =
  LP.serialize32_synth
    _
    synth_named_groups
    _
    (LP.serialize32_bounded_vldata_strong 2 65535
      (LP.partial_serialize32_list _ named_group_serializer named_group_serializer32 ()))
    synth_named_groups_recip
    (fun x -> synth_named_groups_recip x)
    ()
