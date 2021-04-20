module LowParse.SteelSel.Validate
include LowParse.SteelSel.VParse

module S = Steel.Memory
module SE = Steel.SelEffect
module A = Steel.SelArray

module U32 = FStar.UInt32

noeq
type valid_res_t : Type0 = {
  v_contents: byte_array;
  v_rest: byte_array;
  v_rest_len: (v_rest_len: U32.t { U32.v v_rest_len == A.length v_rest });
}

[@SE.__steel_reduce__]
let valid_res_vprop
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: option valid_res_t)
: Tot SE.vprop
= match res with
  | None -> A.varray a
  | Some _ -> vparse p (Some?.v res).v_contents `SE.star` A.varray (Some?.v res).v_rest

let validator
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
=
  (a: byte_array) ->
  (len: U32.t) ->
  SE.SteelSel (option valid_res_t)
    (A.varray a)
    (valid_res_vprop p a)
    (fun _ -> U32.v len == A.length a)
    (fun h res h' ->
      let s = h (A.varray a) in
      match parse p s, res with
      | None, None ->
        h' (A.varray a) == s
      | Some (v, consumed), Some res ->
//        v == (h' (vparse p res.v_contents) <: t) /\
//        h' (A.varray res.v_rest) == Seq.slice s consumed (A.length a) /\
        A.merge_into res.v_contents res.v_rest a
      | _ -> False
    )

#set-options "--ide_id_info_off"

let validate_total_constant_size
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (sz: U32.t)
: Pure (validator p)
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata = Some ParserKindMetadataTotal /\
    U32.v sz == k.parser_kind_low
  ))
  (ensures (fun _ -> True))
= fun (a: byte_array) (len: U32.t) ->
  parser_kind_prop_equiv k p;
  let m0 = SE.get () in
  if len `U32.lt` sz
  then begin
    assert (None? (parse p (m0 (A.varray a))));
    SE.noop ();
    None
  end else begin
    let split = A.split a sz in
    SE.reveal_star (A.varray (A.pfst split)) (A.varray (A.psnd split));
    let m1 = SE.get #(A.varray (A.pfst split) `SE.star` A.varray (A.psnd split)) () in
    parse_strong_prefix p (m0 (A.varray a)) (m1 (A.varray (A.pfst split)));
    parse_injective p (m0 (A.varray a)) (m1 (A.varray (A.pfst split)));
    intro_vparse p (A.pfst split);
    SE.reveal_star (vparse p (A.pfst split)) (A.varray (A.psnd split));
    let m2 = SE.get #(vparse p (A.pfst split) `SE.star` A.varray (A.psnd split)) () in
    assert (
      let s = m0 (A.varray a) in
      let Some (_, consumed) = parse p s in
      m2 (A.varray (A.psnd split)) == Seq.slice s consumed (A.length a)
    );
    let res = ({
      v_contents = A.pfst split;
      v_rest = A.psnd split;
      v_rest_len = len `U32.sub` sz;
    })
    in
    SE.change_equal_slprop
      (vparse p (A.pfst split) `SE.star` A.varray (A.psnd split))
      (valid_res_vprop p a (Some res));
//    let m3 = SE.get #(valid_res_vprop p a (Some res)) () in
//    assert (A.psnd (m3 (valid_res_vprop p a (Some res))) == m2 (A.varray (A.psnd split)));
    Some res
  end
