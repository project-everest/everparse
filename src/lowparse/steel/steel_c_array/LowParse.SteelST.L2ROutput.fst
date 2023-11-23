module LowParse.SteelST.L2ROutput
open Steel.ST.GenElim

module C = Steel.ST.C.Types
module S = Steel.ST.C.Types.UserStruct

noeq
type l2r_output = {
  ptr: C.scalar_t (AP.t byte);
  len: C.scalar_t SZ.t;
}

noextract
inline_for_extraction
[@@ C.norm_field_attr]
let l2r_output_struct_fields =
  FStar.Set.add "ptr" (FStar.Set.singleton "len")

noextract
inline_for_extraction
[@@ C.norm_field_attr]
let fd_ptr : S.field_t l2r_output_struct_fields = "ptr"

noextract
inline_for_extraction
[@@ C.norm_field_attr]
let fd_len : S.field_t l2r_output_struct_fields = "len"

noextract
inline_for_extraction
[@@ C.norm_field_attr]
let l2r_output_struct_def : S.struct_def l2r_output =
  let field_desc : Steel.ST.C.Types.Struct.Aux.field_description_gen_t (S.field_t l2r_output_struct_fields) = {
    fd_nonempty = S.nonempty_set_nonempty_type fd_ptr l2r_output_struct_fields;
    fd_type = (fun (n: S.field_t l2r_output_struct_fields) -> match n with "ptr" -> C.scalar_t (AP.t byte) | "len" -> C.scalar_t SZ.t);
    fd_typedef = (fun (n: S.field_t l2r_output_struct_fields) -> match n with "ptr" -> C.scalar (AP.t byte) | "len" -> C.scalar SZ.t);
  }
  in {
  fields = l2r_output_struct_fields;
  field_desc = field_desc;
  mk = (fun f -> Mkl2r_output (f fd_ptr) (f fd_len));
  get = (fun x (f: S.field_t l2r_output_struct_fields) -> match f with "ptr" -> x.ptr | "len" -> x.len);
  get_mk = (fun _ _ -> ());
  extensionality = (fun s1 s2 phi -> phi fd_ptr; phi fd_len);
}

type t = C.ref (S.struct_typedef l2r_output_struct_def)

[@@__reduce__]
let vp0
  (x: t)
  (vx: AP.array byte)
: Tot vprop
= exists_ (fun (px: AP.t byte) -> exists_ (fun (va: AP.v byte) ->
    AP.arrayptr px va `star`
    C.pts_to x ({ ptr = C.mk_scalar px; len = C.mk_scalar (AP.len vx) }) `star`
    pure (
     AP.array_of va == vx /\
     AP.array_perm vx == full_perm
 )))

let vp
  x vx
= vp0 x vx

let intro_vp
  (#opened: _)
  (x: t)
  (vx: AP.array byte)
  (px: AP.t byte)
  (va: AP.v byte)
: STGhost unit opened
    (
      AP.arrayptr px va `star`
      C.pts_to x ({ ptr = C.mk_scalar px; len = C.mk_scalar (AP.len vx) })
    )
    (fun _ -> vp x vx)
    (
      AP.array_of va == vx /\
      AP.array_perm vx == full_perm
    )
    (fun _ -> True)
= noop ();
  rewrite (vp0 x vx) (vp x vx)

let vp_perm
  #_ #va x
=
  rewrite
    (vp x va)
    (vp0 x va);
  let _ = gen_elim () in
  rewrite
    (vp0 x va)
    (vp x va)

let len
  #va x
=
  rewrite
    (vp x va)
    (vp0 x va);
  let _ = gen_elim () in
  noop ();
  let plen = S.struct_field x fd_len in
  let len = C.read plen in
  S.unstruct_field x fd_len _;
  drop (S.has_struct_field _ _ _);
  rewrite
    (vp0 x va)
    (vp x va);
  return len

let split
  #va x len
=
  rewrite
    (vp x va)
    (vp0 x va);
  let _ = gen_elim () in
  let pptr = S.struct_field x fd_ptr in
  let res = C.read pptr in
  vpattern_rewrite (fun xptr -> AP.arrayptr xptr _) res;
  let plen = S.struct_field x fd_len in
  let xlen = C.read plen in
  let xlen' = xlen `SZ.sub` len in
  let ptr' = AP.split res len in
  let _ = gen_elim () in
  C.write plen xlen';
  S.unstruct_field x fd_len _;
  drop (S.has_struct_field _ fd_len plen);
  C.write pptr ptr';
  S.unstruct_field x fd_ptr _;
  drop (S.has_struct_field _ _ _);
  let vx' = vpattern_replace (AP.arrayptr ptr') in
  noop ();
  rewrite
    (vp0 x (AP.array_of vx'))
    (vp x (AP.array_of vx'));
  return res

let revert
  y len #vx x
=
  rewrite
    (vp x vx)
    (vp0 x vx);
  let _ = gen_elim () in
  let vx' = AP.join y _ in
  let plen = S.struct_field x fd_len in
  C.write plen len;
  S.unstruct_field x fd_len _;
  drop (S.has_struct_field _ _ _);
  let pptr = S.struct_field x fd_ptr in
  C.write pptr y;
  S.unstruct_field x fd_ptr _;
  drop (S.has_struct_field _ _ _);
  noop ();
  rewrite
    (vp0 x (AP.array_of vx'))
    (vp x (AP.array_of vx'));
  return _
