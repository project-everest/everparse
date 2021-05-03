module LowParse.SteelSel.Validate
include LowParse.SteelSel.VParse
include LowParse.Low.ErrorCode

module S = Steel.Memory
module SE = Steel.SelEffect
module SEA = Steel.SelEffect.Atomic
module A = Steel.SelArray
module AP = Steel.SelArrayPtr

module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* A validator consuming the whole input buffer. Useful for all
   parsers that do not have the strong prefix property, in particular
   those marked ConsumesAll. *)

let tvalid_res_vprop
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: bool)
: Tot SE.vprop
= if res
  then vparse p a
  else AP.varrayptr a

unfold
let tvalid_res_vprop_true
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: bool)
  (x: SE.t_of (tvalid_res_vprop p a res))
: Pure (v t)
  (requires (res == true))
  (ensures (fun _ -> True))
= x

unfold
let tvalid_res_vprop_false
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: bool)
  (x: SE.t_of (tvalid_res_vprop p a res))
: Pure (AP.v byte)
  (requires (res == false))
  (ensures (fun _ -> True))
= x

let tvalidator
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
=
  (a: byte_array) ->
  (len: U32.t) ->
  SE.SteelSel bool
    (AP.varrayptr a)
    (tvalid_res_vprop p a)
    (fun h -> U32.v len == A.length (h (AP.varrayptr a)).AP.array)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      let s' = h' (tvalid_res_vprop p a res) in
      (res == true <==> valid p s.AP.contents) /\
      begin if res
      then
        let s' = tvalid_res_vprop_true p a res s' in
        s'.array == s.AP.array /\
        is_byte_repr p s'.contents s.AP.contents
      else
        let s' = tvalid_res_vprop_false p a res s' in
        s' == s
      end
    )

(* A validator that returns the number of bytes consumed. Contrary to
   LowParse.Low validators, this validator can be used only if the
   parser has the "weak prefix property" (TODO): if a parser does not
   consume all bytes from some input buffer, then it does not depend on
   any bytes past what it consumed.
 *)

let wvalidator
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
=
  (a: byte_array) ->
  (len: U32.t) ->
  SE.SteelSel U64.t
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun h -> U32.v len == A.length (h (AP.varrayptr a)).AP.array)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      h' (AP.varrayptr a) == s /\
      begin if is_error res
      then
        None? (parse p s.AP.contents)
      else
        U64.v res <= Seq.length s.AP.contents /\
        valid p (Seq.slice s.AP.contents 0 (U64.v res))
      end
    )

let wvalidate_vprop
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: option byte_array)
: Tot SE.vprop
= if Some? res
  then vparse p a `SE.star` AP.varrayptr (Some?.v res)
  else AP.varrayptr a

unfold
let wvalidate_vprop_some
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: option byte_array)
  (x: SE.t_of (wvalidate_vprop p a res))
: Pure (v t & AP.v byte)
  (requires (Some? res))
  (ensures (fun _ -> True))
= x

unfold
let wvalidate_vprop_none
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: option byte_array)
  (x: SE.t_of (wvalidate_vprop p a res))
: Pure (AP.v byte)
  (requires (None? res))
  (ensures (fun _ -> True))
= x

let wvalidate_post // FIXME: WHY WHY WHY do I need to define this postcondition separately? (if not, then dummy fails to verify)
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (len: U32.t)
  (res: option byte_array)
  (s: AP.v byte)
  (s': SE.t_of (wvalidate_vprop p a res))
: Tot prop
=
  if None? res
  then
    None? (parse p s.AP.contents) /\
    wvalidate_vprop_none p a res s' == s
  else
    let v = wvalidate_vprop_some p a res s' in
    let vl = fst v in
    let vr = snd v in
    let consumed = A.length vl.array in
    len == A.len s.AP.array /\
    A.merge_into vl.array vr.AP.array s.AP.array /\
    A.length vl.array == consumed /\
    is_byte_repr p vl.contents (Seq.slice s.AP.contents 0 consumed) /\
    vr.AP.contents == Seq.slice s.AP.contents consumed (U32.v len)

val wvalidate
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (w: wvalidator p)
  (a: byte_array)
  (len: U32.t)
: SE.SteelSel (option byte_array)
    (AP.varrayptr a)
    (wvalidate_vprop p a)
    (fun h -> len == A.len (h (AP.varrayptr a)).AP.array)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      let s'  = h' (wvalidate_vprop p a res) in
      wvalidate_post p a len res s s'
    )

let wvalidate
  #t #k #p w a len
=
  let consumed = w a len in
  if is_success consumed
  then begin
    let ar = AP.split a (uint64_to_uint32 consumed) in
    intro_vparse p a;
    let res = Some ar in
    SEA.reveal_star (vparse p a) (AP.varrayptr ar);
    SEA.change_equal_slprop
      (vparse p a `SE.star` AP.varrayptr ar)
      (wvalidate_vprop p a res);
    SEA.return res
  end else begin
    SEA.change_equal_slprop
      (AP.varrayptr a)
      (wvalidate_vprop p a None);
    SEA.return None
  end

let dummy
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (w: wvalidator p)
  (a: byte_array)
  (len: U32.t)
: SE.SteelSel unit
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun h -> len == A.len (h (AP.varrayptr a)).AP.array)
    (fun h _ h' ->
      h' (AP.varrayptr a) == h (AP.varrayptr a)
    )
=
  let g0 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  let res = wvalidate w a len in
  if None? res
  then begin
    SEA.change_equal_slprop
      (wvalidate_vprop p a res)
      (AP.varrayptr a);
    SEA.return ()
  end else begin
    let ar = Some?.v res in
    SEA.change_equal_slprop
      (wvalidate_vprop p a res)
      (vparse p a `SE.star` AP.varrayptr ar);
    SEA.reveal_star (vparse p a) (AP.varrayptr ar);
    let g1 : Ghost.erased (v t) = SEA.gget (vparse p a) in
    elim_vparse p a;
    let g2 = SEA.gget (AP.varrayptr a) in
    let glen = Ghost.hide (A.length (Ghost.reveal g1).array) in
    is_byte_repr_injective p (Ghost.reveal g1).contents (Seq.slice (Ghost.reveal g0).AP.contents 0 (Ghost.reveal glen)) (Ghost.reveal g2).AP.contents;
    Seq.lemma_split (Ghost.reveal g0).AP.contents (Ghost.reveal glen);
    AP.join a ar
  end

(*
      match parse p s, res with
      | None, None ->
        h' (A.varray a) == s
      | Some (v, consumed), Some res ->
//        v == (h' (vparse p res.v_contents) <: t) /\
//        h' (A.varray res.v_rest) == Seq.slice s consumed (A.length a) /\
        A.merge_into res.v_contents res.v_rest a
      | _ -> False
    )
  

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
