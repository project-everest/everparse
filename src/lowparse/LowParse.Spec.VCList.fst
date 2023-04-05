(* Variable-count lists *)

module LowParse.Spec.VCList
include LowParse.Spec.Combinators // for seq_slice_append_l
include LowParse.Spec.Array // for vlarray

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot

let parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (y: parser (parse_nlist_kind n k) (nlist n t) { y == parse_nlist' n p } )
= parse_nlist' n p

#push-options "--z3rlimit 32"
#restart-solver

let rec parse_nlist_sum
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n1 n2: nat)
  (b: bytes)
: Lemma
  (ensures (parse (parse_nlist (n1 + n2) p) b ==
    begin match parse (parse_nlist n1 p) b with
    | None -> None
    | Some (l1, consumed1) ->
      let b2 = Seq.slice b consumed1 (Seq.length b) in
      match parse (parse_nlist n2 p) b2 with
      | None -> None
      | Some (l2, consumed2) ->
        List.Tot.append_length l1 l2;
        Some (l1 `List.Tot.append` l2, consumed1 + consumed2)
    end
  ))
  (decreases n1)
= parse_nlist_eq n1 p b;
  parse_nlist_eq (n1 + n2) p b;
  if n1 = 0
  then ()
  else
    match parse p b with
    | None -> ()
    | Some (x, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      parse_nlist_sum p (n1 - 1) n2 b'

#pop-options

let serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (y: serializer (parse_nlist n p) { y == serialize_nlist' n s })
= serialize_nlist' n s
