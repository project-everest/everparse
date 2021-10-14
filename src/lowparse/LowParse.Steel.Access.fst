module LowParse.Steel.Access
include LowParse.Steel.VParse

module S = Steel.Memory
module SP = Steel.FractionalPermission
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module AP = LowParse.Steel.ArrayPtr
module SZ = Steel.C.StdInt.Base


let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (Type u#1)
=
  (base: Type) ->
  (a: byte_array base) ->
  SE.Steel SZ.size_t
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun h ->
      Some? (parse p (h (AP.varrayptr a)).AP.contents)
    )
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      h' (AP.varrayptr a) == s /\
      begin match parse p s.AP.contents with
      | None -> False
      | Some (_, consumed) -> SZ.size_v res == consumed
      end
    )

let parsed_size_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (parsed_size p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      SZ.size_v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun base a ->
  parser_kind_prop_equiv k p;
  let g : Ghost.erased (AP.v base byte) = SEA.gget (AP.varrayptr a) in
  assert (Some? (parse p g.AP.contents));
  SEA.return sz

let get_parsed_size
  (#base: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (a: byte_array base)
: SE.Steel SZ.size_t
    (vparse p a)
    (fun _ -> vparse p a)
    (fun _ -> True)
    (fun h res h' ->
      h' (vparse p a) == h (vparse p a) /\
      SZ.size_v res == AP.length (array_of (h (vparse p a)))
    )
=
  elim_vparse p a;
  let _ = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY is this needed?
  let res = j base a in
  intro_vparse p a;
  SEA.return res

let peek_strong
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (a: byte_array base)
: SE.Steel (byte_array base)
    (AP.varrayptr a)
    (fun res -> vparse p a `SE.star` AP.varrayptr res)
    (fun h ->
      k.parser_kind_subkind == Some ParserStrong /\
      Some? (parse p (h (AP.varrayptr a)).AP.contents)
    )
    (fun h res h' ->
      let c_a = h (AP.varrayptr a) in
      let c_a' = h' (vparse p a) in
      let c_res = h' (AP.varrayptr res) in
      let consumed = AP.length (array_of c_a') in
      AP.merge_into (array_of c_a') c_res.AP.array c_a.AP.array /\
//      perm_of c_a' == c_a.AP.perm /\
//      c_res.AP.perm == c_a.AP.perm /\
      is_byte_repr p c_a'.contents (Seq.slice c_a.AP.contents 0 consumed) /\
      consumed <= AP.length c_a.AP.array /\
      c_res.AP.contents == Seq.slice c_a.AP.contents consumed (AP.length c_a.AP.array)
    )
=
  let c_a : Ghost.erased (AP.v base byte) = SEA.gget (AP.varrayptr a) in
  let n = j base a in
  parse_strong_prefix p c_a.AP.contents (Seq.slice c_a.AP.contents 0 (SZ.size_v n)); 
  let res = AP.split a n in
  intro_vparse p a;
  SEA.return res

val memcpy
  (#base_dst #base_src: _)
  (dst: byte_array base_dst)
  (src: byte_array base_src)
  (n: SZ.size_t)
: SE.Steel (byte_array base_dst)
    (AP.varrayptr dst `SE.star` AP.varrayptr src)
    (fun _ -> AP.varrayptr dst `SE.star` AP.varrayptr src)
    (fun h ->
//      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      SZ.size_v n <= AP.length (h (AP.varrayptr src)).AP.array /\
      SZ.size_v n <= AP.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h res h' ->
      let s = h (AP.varrayptr src) in
      let d = h (AP.varrayptr dst) in
      let d' = h' (AP.varrayptr dst) in
      res == dst /\
      h' (AP.varrayptr src) == s /\
//      d'.AP.perm == SP.full_perm /\
      d'.AP.array == d.AP.array /\
      SZ.size_v n <= AP.length d.AP.array /\
      SZ.size_v n <= AP.length s.AP.array /\
      d'.AP.contents `Seq.equal` (Seq.slice s.AP.contents 0 (SZ.size_v n) `Seq.append` Seq.slice d.AP.contents (SZ.size_v n) (AP.length d.AP.array))
    )
    (decreases (SZ.size_v n))

let rec memcpy dst src n =
//  let g : Ghost.erased (AP.v base_dst byte) = SEA.gget (AP.varrayptr dst) in
//  assert (g.AP.perm == SP.full_perm);
  if n = SZ.zero_size
  then SEA.return dst
  else begin
    let j = n `SZ.size_sub` SZ.one_size in
    let c = AP.index src j in
    AP.upd dst j c;
    memcpy dst src j
  end

val copy_exact
  (#base_src #base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array base_src)
  (dst: byte_array base_dst)
  (n: SZ.size_t)
: SE.Steel unit
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun _ -> vparse p src `SE.star` vparse p dst)
    (fun h ->
//      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      SZ.size_v n == AP.length (array_of (h (vparse p src))) /\
      SZ.size_v n == AP.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h _ h' ->
      let s = h (vparse p src) in
      let d = h (AP.varrayptr dst) in
      let d' = h' (vparse p dst) in
      SZ.size_v n == AP.length (array_of s) /\
      SZ.size_v n == AP.length d.AP.array /\
      h' (vparse p src) == s /\
      array_of d' == d.AP.array /\
//      perm_of d' == SP.full_perm /\
      d'.contents == s.contents
    )

let copy_exact #base_src #base_dst p src dst n =
  elim_vparse p src;
  let _ = memcpy dst src n in
  let gs : Ghost.erased (AP.v base_src byte) = SEA.gget (AP.varrayptr src) in
  let gd : Ghost.erased (AP.v base_dst byte) = SEA.gget (AP.varrayptr dst) in
  assert (gd.AP.contents `Seq.equal` gs.AP.contents);
  intro_vparse p src;
  intro_vparse p dst

val copy_strong
  (#base_src #base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array base_src)
  (dst: byte_array base_dst)
: SE.Steel (byte_array base_dst)
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun res -> vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res)
    (fun h ->
//      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      AP.length (array_of (h (vparse p src))) <= AP.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h res h' ->
      SE.can_be_split (vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res) (vparse p src) /\ // FIXME: WHY WHY WHY?
      SE.can_be_split (vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res) (vparse p dst) /\ // same here
      begin
        let s = h (vparse p src) in
        let d = h (AP.varrayptr dst) in
        let d' = h' (vparse p dst) in
        let r = h' (AP.varrayptr res) in
        h' (vparse p src) == s /\
        AP.merge_into (array_of d') r.AP.array d.AP.array /\
        d'.contents == s.contents /\
//        perm_of d' == SP.full_perm /\
        AP.length (array_of s) == AP.length (array_of d') /\ // TODO: this should be a consequence of the equality of the contents, via parser injectivity
//        r.AP.perm == SP.full_perm /\
        r.AP.contents == Seq.slice d.AP.contents (AP.length (array_of s)) (AP.length d.AP.array)
      end
    )

let copy_strong #_ #_ #_ #_ #p j src dst =
  let n = get_parsed_size j src in
  let res = AP.split dst n in
  copy_exact p src dst n;
  SEA.reveal_star_3 (vparse p src) (vparse p dst) (AP.varrayptr res); // for can_be_split
  SEA.return res

// [@@SEA.__steel_reduce__]
let copy_weak_vprop
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array base_src)
  (dst: byte_array base_dst)
  (res: option (byte_array base_dst))
: Tot SE.vprop
= vparse p src `SE.star`
  begin if None? res
  then AP.varrayptr dst
  else vparse p dst `SE.star` AP.varrayptr (Some?.v res)
  end

unfold
let copy_weak_vprop_src
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array base_src)
  (dst: byte_array base_dst)
  (res: option (byte_array base_dst))
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Tot (v base_src k t)
= fst x

unfold
let copy_weak_vprop_dst_some
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array base_src)
  (dst: byte_array base_dst)
  (res: option (byte_array base_dst))
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Pure (v base_dst k t)
  (requires (None? res == false))
  (ensures (fun _ -> True))
= fst #(SE.t_of (vparse p dst)) #(SE.t_of (AP.varrayptr (Some?.v res))) (snd x)

unfold
let copy_weak_vprop_dst_none
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array base_src)
  (dst: byte_array base_dst)
  (res: option (byte_array base_dst))
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Pure (AP.v base_dst byte)
  (requires (None? res))
  (ensures (fun _ -> True))
= snd x

unfold
let copy_weak_vprop_res
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: (byte_array base_src))
  (dst: (byte_array base_dst))
  (res: option (byte_array base_dst))
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Pure (AP.v base_dst byte)
  (requires (Some? res))
  (ensures (fun _ -> True))
= snd #(SE.t_of (vparse p dst)) #(SE.t_of (AP.varrayptr (Some?.v res))) (snd x)

let copy_weak_post
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: (byte_array base_src))
  (dst: (byte_array base_dst))
  (h: SE.rmem (vparse p src `SE.star` AP.varrayptr dst))
  (res0: option (byte_array base_dst))
  (h': SE.rmem (copy_weak_vprop p src dst res0))
: Tot prop
=
      let x = h' (copy_weak_vprop p src dst res0) in
      h (vparse p src) == copy_weak_vprop_src p src dst res0 x /\
      begin
        if None? res0
        then
          copy_weak_vprop_dst_none p src dst res0 x == h (AP.varrayptr dst)
        else
          let res = Some?.v res0 in
          let s = h (vparse p src) in
          let d' = copy_weak_vprop_dst_some p src dst res0 x in
          let d = h (AP.varrayptr dst) in
          let r = copy_weak_vprop_res p src dst res0 x in
          AP.merge_into (array_of d') r.AP.array d.AP.array /\
//          perm_of d' == SP.full_perm /\
          d'.contents == s.contents /\
          AP.length (array_of s) == AP.length (array_of d') /\ // TODO: this should be a consequence of the equality of the contents, via parser injectivity
//          r.AP.perm == SP.full_perm /\
          r.AP.contents == Seq.slice d.AP.contents (AP.length (array_of s)) (AP.length d.AP.array)
      end

val copy_weak
  (#base_src: Type)
  (#base_dst: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: (byte_array base_src))
  (dst: (byte_array base_dst))
  (n: SZ.size_t)
: SE.Steel (option (byte_array base_dst))
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun res -> copy_weak_vprop p src dst res)
    (fun h ->
//      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      AP.length (h (AP.varrayptr dst)).AP.array == SZ.size_v n
    )
    (fun h res0 h' ->
      copy_weak_post p src dst h res0 h'
    )

let copy_weak #base_src #base_dst #_ #_ #p j src dst n_dst =
  let n_src = get_parsed_size j src in
  if not (n_src `SZ.size_le` n_dst) // n_dst `SZ.size_lt` n_src
  then begin
    SEA.reveal_star (vparse p src) (AP.varrayptr dst);
    let res0 : option (byte_array base_dst) = None in
    SEA.change_equal_slprop
      (vparse p src `SE.star` AP.varrayptr dst)
      (copy_weak_vprop p src dst res0);
    SEA.return res0
  end else begin
    let res = AP.split dst n_src in
    copy_exact p src dst n_src;
    SEA.reveal_star (vparse p dst) (AP.varrayptr res);
    SEA.reveal_star (vparse p src) (vparse p dst `SE.star` AP.varrayptr res);
    let res0 = Some res in
    SEA.change_equal_slprop
      (vparse p src `SE.star` (vparse p dst `SE.star` AP.varrayptr res))
      (copy_weak_vprop p src dst res0);
    SEA.return res0
  end

module R2L = LowParse.Steel.R2LOutput

val copy_strong_r2l
  (#base_src #base_dst: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array base_src)
  (dst: R2L.t base_dst)
: SE.Steel (byte_array base_dst)
    (vparse p src `SE.star` R2L.vp dst)
    (fun res -> vparse p src `SE.star` R2L.vp dst `SE.star` vparse p res)
    (fun h ->
      AP.length (array_of (h (vparse p src))) <= AP.length (h (R2L.vp dst))
    )
    (fun h res h' ->
      SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` vparse p res) (vparse p src) /\ // FIXME: WHY WHY WHY?
      SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` vparse p res) (R2L.vp dst) /\ // same here
      begin
        let s = h (vparse p src) in
        let d = h (R2L.vp dst) in
        let d' = h' (R2L.vp dst) in
        let r = h' (vparse p res) in
        h' (vparse p src) == s /\
        AP.merge_into d' (array_of r) d /\
//        (perm_of r) == SP.full_perm /\
        r.contents == s.contents /\
        AP.length (array_of s) == AP.length (array_of r) // TODO: this should be a consequence of the equality of the contents, via parser injectivity
      end
    )

let copy_strong_r2l #_ #_ #_ #_ #p j src dst =
  let n = get_parsed_size j src in
  let res = R2L.split dst n in
  copy_exact p src res n;
  SEA.reveal_star_3 (vparse p src) (R2L.vp dst) (vparse p res); // for can_be_split
  SEA.return res

(* TODO: generalize somehow to any vprop on option. *)

let copy_weak_r2l_vprop
  (#base: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (res: option (byte_array base))
: Tot SE.vprop
= if None? res
  then SE.emp
  else vparse p (Some?.v res)

unfold
let copy_weak_r2l_vprop_res
  (#base: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (res: option (byte_array base))
  (x: SE.t_of (copy_weak_r2l_vprop p res))
: Pure (v base k t)
  (requires (Some? res))
  (ensures (fun _ -> True))
= x

let copy_weak_r2l_post
  (#base_src #base_dst: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array base_src)
  (dst: R2L.t base_dst)
  (h: SE.rmem (vparse p src `SE.star` R2L.vp dst))
  (res0: option (byte_array base_dst))
  (h': SE.rmem (vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res0))
: Tot prop
=
  SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res0) (vparse p src) /\
  SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res0) (R2L.vp dst) /\
  begin
      let s = h (vparse p src) in
      let d = h (R2L.vp dst) in
      let d' = h' (R2L.vp dst) in
      h' (vparse p src) == s /\
      begin
        if None? res0
        then
           d' == d
        else
          let res = Some?.v res0 in
          let r = copy_weak_r2l_vprop_res p res0 (h' (copy_weak_r2l_vprop p res0)) in
          AP.merge_into d' (array_of r) d /\
//          perm_of r == SP.full_perm /\
          r.contents == s.contents /\
          AP.length (array_of s) == AP.length (array_of r) // TODO: this should be a consequence of the equality of the contents, via parser injectivity
      end
  end

val copy_weak_r2l
  (#base_src #base_dst: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array base_src)
  (dst: R2L.t base_dst)
: SE.Steel (option (byte_array base_dst))
    (vparse p src `SE.star` R2L.vp dst)
    (fun res -> vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res)
    (fun _ -> True)
    (fun h res0 h' ->
      copy_weak_r2l_post p src dst h res0 h'
    )

let copy_weak_r2l #base_src #base_dst #_ #_ #p j src dst =
  let n_dst = R2L.len dst in
  let n_src = get_parsed_size j src in
  if not (n_src `SZ.size_le` n_dst) // n_dst `U32.lt` n_src
  then begin
    let res0 : option (byte_array base_dst) = None in
    SEA.change_equal_slprop
      SE.emp
      (copy_weak_r2l_vprop p res0);
    SEA.reveal_star_3 (vparse p src) (R2L.vp dst) (copy_weak_r2l_vprop p res0);
    SEA.return res0
  end else begin
    let res = R2L.split dst n_src in
    copy_exact p src res n_src;
    let res0 = Some res in
    SEA.change_equal_slprop
      (vparse p res)
      (copy_weak_r2l_vprop p res0);
    SEA.reveal_star_3 (vparse p src) (R2L.vp dst) (copy_weak_r2l_vprop p res0);
    SEA.return res0
  end
