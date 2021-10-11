module LowParse.Steel.R2LOutput
include LowParse.Bytes

module S = Steel.Memory
module SP = Steel.FractionalPermission
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.C.Array
module AP = LowParse.Steel.ArrayPtr
module SZ = Steel.C.StdInt

(* Right-to-left output buffer *)

val t (base: Type0): Type0

val null (base: Type) : t base

val g_is_null (#base: Type) (x: t base) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> x == null base))

val vp_hp
  (#base: Type)
  (x: t base)
: Tot (S.slprop u#1)

val vp_sel
  (#base: Type)
  (x: t base)
: Tot (SE.selector (A.array base byte) (vp_hp x))

[@SE.__steel_reduce__]
let vp' 
  (#base: Type)
  (x: t base)
: Tot SE.vprop'
= {
  SE.hp = vp_hp x;
  SE.t = A.array base byte;
  SE.sel = vp_sel x;
}

[@SE.__steel_reduce__]
let vp
  (#base: Type)
  (x: t base)
: Tot SE.vprop
= SE.VUnit (vp' x)

val vp_not_null
  (#opened: _)
  (#base: Type)
  (x: t base)
: SEA.SteelGhost unit opened
    (vp x)
    (fun _ -> vp x)
    (fun _ -> True)
    (fun h _ h' ->
      h' (vp x) == h (vp x) /\
      g_is_null x == false
    )

val vp_or_null_hp
  (#base: Type)
  (x: t base)
: Tot (S.slprop u#1)

val vp_or_null_sel
  (#base: Type)
  (x: t base)
: Tot (SE.selector (option (A.array base byte)) (vp_or_null_hp x))

[@SE.__steel_reduce__]
let vp_or_null' 
  (#base: Type)
  (x: t base)
: Tot SE.vprop'
= {
  SE.hp = vp_or_null_hp x;
  SE.t = option (A.array base byte);
  SE.sel = vp_or_null_sel x;
}

[@SE.__steel_reduce__]
let vp_or_null
  (#base: Type)
  (x: t base)
: Tot SE.vprop
= SE.VUnit (vp_or_null' x)

val intro_vp_or_null_none
  (#opened: _)
  (#base: Type)
  (x: t base)
: SEA.SteelGhost unit opened
    SE.emp
    (fun _ -> vp_or_null x)
    (fun _ -> g_is_null x == true)
    (fun _ _ h' -> h' (vp_or_null x) == None)

val intro_vp_or_null_some
  (#opened: _)
  (#base: Type)
  (x: t base)
: SEA.SteelGhost unit opened
    (vp x)
    (fun _ -> vp_or_null x)
    (fun _ -> True)
    (fun h _ h' ->
      g_is_null x == false /\
      h' (vp_or_null x) == Some (h (vp x)
    ))

val elim_vp_or_null_some
  (#opened: _)
  (#base: Type)
  (x: t base)
: SEA.SteelGhost unit opened
    (vp_or_null x)
    (fun _ -> vp x)
    (fun h -> g_is_null x == false \/ Some? (h (vp_or_null x)))
    (fun h _ h' ->
      g_is_null x == false /\
      h (vp_or_null x) == Some (h' (vp x))
    )

val elim_vp_or_null_none
  (#opened: _)
  (#base: Type)
  (x: t base)
: SEA.SteelGhost unit opened
    (vp_or_null x)
    (fun _ -> SE.emp)
    (fun h -> g_is_null x == true \/ None? (h (vp_or_null x)))
    (fun h _ _ ->
      g_is_null x == true /\
      h (vp_or_null x) == None
    )

val is_null
  (#opened: _)
  (#base: Type)
  (x: t base)
: SEA.SteelAtomicBase bool false opened SEA.Unobservable
    (vp_or_null x)
    (fun _ -> vp_or_null x)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (vp_or_null x) in
      h' (vp_or_null x) == s /\
      res == None? s /\
      res == g_is_null x
    )

let make_vprop_post
  (#base: Type)
  (x: AP.t base byte)
  (res: t base)
: Tot SE.vprop
= 
  if g_is_null res then AP.varrayptr x else SE.emp

val make
  (#base: Type)
  (x: AP.t base byte)
  (len: SZ.size_t)
: SE.Steel (t base)
    (AP.varrayptr x)
    (fun res -> vp_or_null res `SE.star` make_vprop_post x res)
    (fun h ->
//      (h (AP.varrayptr x)).AP.perm == SP.full_perm /\
      A.length (h (AP.varrayptr x)).AP.array == SZ.size_v len
    )
    (fun h res h' ->
      let s = h' (vp_or_null res) in
      g_is_null res == None? s /\
      (g_is_null res == true ==> h' (AP.varrayptr x) == h (AP.varrayptr x)) /\
      (g_is_null res == false ==> (
        Some? s /\
        (Some?.v s) == (h (AP.varrayptr x)).AP.array /\
        A.length (Some?.v s) == SZ.size_v len
      ))
    )

val alloc
  (len: SZ.size_t)
: SE.Steel (t (AP.base_t byte len))
    SE.emp
    (fun res -> vp_or_null res)
    (fun _ -> SZ.size_v len > 0)
    (fun _ res h' ->
      match g_is_null res, h' (vp_or_null res) with
      | true, None -> True
      | false, Some a ->
        A.length a == SZ.size_v len /\
        A.freeable a
      | _ -> False
    )

(*
=
  let x = AP.alloc 0uy len in
  if AP.is_null x
  then begin
    AP.elim_varrayptr_or_null_none x;
    intro_vp_or_null_none null;
    SEA.return null
  end else begin
    AP.elim_varrayptr_or_null_some x;
    let g : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr x) in
    assert (g.AP.perm == Steel.FractionalPermission.full_perm);
    let res = make x len in
    if is_null res
    then begin
      SEA.change_equal_slprop
        (if g_is_null res then AP.varrayptr x else SE.emp)
        (AP.varrayptr x);
      AP.free x
    end else begin
      SEA.noop ();
      SEA.change_equal_slprop
        (if g_is_null res then AP.varrayptr x else SE.emp)
        SE.emp
    end;
    SEA.return res
  end
*)

val len
  (#base: Type)
  (x: t base)
: SE.Steel SZ.size_t
    (vp x)
    (fun _ -> vp x)
    (fun _ -> True)
    (fun h len h' ->
      h (vp x) == h' (vp x) /\
      A.length (h' (vp x)) == SZ.size_v len
    )

val split
  (#base: Type)
  (x: t base)
  (len: SZ.size_t)
: SE.Steel (AP.t base byte)
    (vp x)
    (fun res -> vp x `SE.star` AP.varrayptr res)
    (fun h -> SZ.size_v len <= A.length (h (vp x)))
    (fun h res h' ->
      let ar = (h' (AP.varrayptr res)).AP.array in
//      (h' (AP.varrayptr res)).AP.perm == SP.full_perm /\
      A.merge_into (h' (vp x)) ar (h (vp x)) /\
      A.length ar == SZ.size_v len
    )

val merge
  (#base: Type)
  (x: t base)
  (y: AP.t base byte)
  (len: SZ.size_t)
: SE.Steel unit
    (vp x `SE.star` AP.varrayptr y)
    (fun res -> vp x)
    (fun h ->
      let ar = (h (AP.varrayptr y)).AP.array in
//      (h (AP.varrayptr y)).AP.perm == SP.full_perm /\
      SZ.size_v len == A.length ar /\
      A.adjacent (h (vp x)) ar
    )
    (fun h _ h' ->
      A.merge_into (h (vp x)) (h (AP.varrayptr y)).AP.array (h' (vp x))
    )

val free
  (#base: Type)
  (x: t base)
: SE.Steel unit
    (vp x)
    (fun _ -> SE.emp)
    (fun h -> A.freeable (h (vp x)))
    (fun _ _ _ -> True)
