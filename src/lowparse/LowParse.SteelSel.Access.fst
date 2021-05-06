module LowParse.SteelSel.Access
include LowParse.SteelSel.VParse

module S = Steel.Memory
module SE = Steel.SelEffect
module SEA = Steel.SelEffect.Atomic
module A = Steel.SelArray
module AP = Steel.SelArrayPtr

module U32 = FStar.UInt32

let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
= (a: byte_array) ->
  SE.SteelSel U32.t
    (vparse p a)
    (fun _ -> vparse p a)
    (fun _ -> True)
    (fun h res h' ->
      h' (vparse p a) == h (vparse p a) /\
      U32.v res == A.length (h (vparse p a)).array
    )

let parsed_size_total_constant_size' // OK, but mostly not used
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t)
: Pure (parsed_size p)
    (requires (
      k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal /\
      U32.v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun a ->
  elim_vparse p a;
  let _ = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY is this needed?
  parser_kind_prop_equiv k p;
  intro_vparse p a;
  SEA.return sz

let strong_parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
= (a: byte_array) ->
  SE.SteelSel U32.t
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      h' (AP.varrayptr a) == s /\
      begin match parse p s.AP.contents with
      | None -> False
      | Some (_, consumed) -> U32.v res == consumed
      end
    )

let get_parsed_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: strong_parsed_size p)
: Tot (parsed_size p)
=
  fun a ->
  elim_vparse p a;
  let _ = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY is this needed?
  let res = j a in
  intro_vparse p a;
  SEA.return res

let peek_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: strong_parsed_size p)
  (a: byte_array)
: SE.SteelSel byte_array
    (AP.varrayptr a)
    (fun res -> vparse p a `SE.star` AP.varrayptr res)
    (fun _ -> k.parser_kind_subkind == Some ParserStrong)
    (fun h res h' ->
      let c_a = h (AP.varrayptr a) in
      let c_a' = h' (vparse p a) in
      let c_res = h' (AP.varrayptr res) in
      let consumed = A.length c_a'.array in
      A.merge_into c_a'.array c_res.AP.array c_a.AP.array /\
      is_byte_repr p c_a'.contents (Seq.slice c_a.AP.contents 0 consumed) /\
      c_res.AP.contents == Seq.slice c_a.AP.contents consumed (A.length c_a.AP.array)
    )
=
  let c_a = SEA.gget (AP.varrayptr a) in
  let n = j a in
  parse_strong_prefix p c_a.AP.contents (Seq.slice c_a.AP.contents 0 (U32.v n)); 
  let res = AP.split a n in
  intro_vparse p a;
  SEA.return res
