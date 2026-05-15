module CBOR.Pulse.API.Det.C
#lang-pulse

(* Implementation of the CBOR.Pulse.API.Det.C interface using the new
   EverParse-based stack (CBOR.Pulse.Raw.EverParse.Det.Impl).

   This file delegates most operations to Det.Impl, with thin
   ArrayPtr ↔ Slice conversion wrappers where the API exposes
   ArrayPtr but Det.Impl works on Slice. *)

module Impl = CBOR.Pulse.Raw.EverParse.Det.Impl
module SU = Pulse.Lib.Slice.Util

(* ======== Match relation and basic ops ======== *)

[@@pulse_unfold]
let cbor_det_match = Impl.cbor_det_match

let cbor_det_reset_perm = Impl.cbor_det_reset_perm

let cbor_det_share = Impl.cbor_det_share

let cbor_det_gather = Impl.cbor_det_gather

(* ======== Validate, parse, size, serialize ======== *)

fn cbor_det_validate
  (input: AP.ptr U8.t)
  (input_len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (SZ.v input_len == Seq.length v))
returns res: SZ.t
ensures
    (pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))
{
  let s = SU.arrayptr_to_slice_intro_trade input input_len;
  let res = Impl.cbor_det_validate () s;
  Trade.elim _ (pts_to input #pm v);
  res
}

module ID = FStar.IndefiniteDescription

let cbor_det_validate_success_elim
  (len: SZ.t)
  (v: Seq.seq U8.t)
: Pure (Ghost.erased (Spec.cbor & Seq.seq U8.t))
    (requires exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1))
    (ensures fun (v1, v2) ->
      Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    )
= let v1 = ID.indefinite_description_tot _ (fun v1 -> exists v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)) in
  let v2 = ID.indefinite_description_tot _ (fun v2 -> Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)) in
  (Ghost.reveal v1, Ghost.reveal v2)

fn cbor_det_parse
  (input: AP.ptr U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    ))
returns res: cbor_det_t
ensures
    (exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == Spec.cbor_det_serialize v'
    ))
{
  let v1v2 = cbor_det_validate_success_elim len v;
  assert (pure (Seq.equal (Seq.slice v 0 (SZ.v len)) (Spec.cbor_det_serialize (fst v1v2))));
  let gr : Ghost.erased (AP.ptr U8.t) = AP.ghost_split input len;
  intro
    (Trade.trade
      (pts_to input #pm (Seq.slice v 0 (SZ.v len)))
      (pts_to input #pm v)
    )
    #(pts_to (Ghost.reveal gr) #pm (Seq.slice v (SZ.v len) (Seq.length v)))
    fn _
  {
    Seq.lemma_split v (SZ.v len);
    AP.join input gr
  };
  Seq.append_empty_r (Spec.cbor_det_serialize (fst v1v2));
  let s = SU.arrayptr_to_slice_intro_trade input len;
  Trade.trans _ _ (pts_to input #pm v);
  S.pts_to_len s;
  let res = Impl.cbor_det_parse_valid () s;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

let cbor_det_size = Impl.cbor_det_size

#restart-solver
fn cbor_det_serialize
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
norewrite
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      SZ.v output_len == Seq.length v /\
      cbor_det_serialize_fits_postcond y res v
    ))
{
  Impl.cbor_det_serialize_arrayptr x output output_len
}

#restart-solver
fn cbor_det_serialize_safe
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
norewrite
requires
    (cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v))
returns res: SZ.t
ensures
    (exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      SZ.v output_len == Seq.length v' /\
      cbor_det_serialize_postcond_c y v v' res
    ))
{
  Impl.cbor_det_serialize_safe_arrayptr x output output_len
}

(* ======== UTF8 ======== *)

fn cbor_det_impl_utf8_correct_from_array (_: unit) : cbor_det_impl_utf8_correct_from_array_t
=
  (s: _)
  (len: _)
  (#p: _)
  (#v: _)
{
  let sl = S.arrayptr_to_slice_intro s len;
  S.pts_to_len sl;
  let res = CBOR.Pulse.API.UTF8.impl_utf8_correct sl;
  S.arrayptr_to_slice_elim sl;
  res
}

(* ======== Constructors ======== *)

let cbor_det_mk_simple_value = Impl.cbor_det_mk_simple_value
let cbor_det_mk_int64 = Impl.cbor_det_mk_int64
let cbor_det_mk_tagged = Impl.cbor_det_mk_tagged

let cbor_det_mk_byte_string_from_arrayptr (_: unit) =
  mk_string_from_arrayptr (Impl.cbor_det_mk_string ()) cbor_major_type_byte_string

let cbor_det_mk_text_string_from_arrayptr (_: unit) =
  mk_string_from_arrayptr (Impl.cbor_det_mk_string ()) cbor_major_type_text_string

let cbor_det_mk_array_from_array () : mk_array_from_array_t cbor_det_match
  = mk_array_from_array (Impl.cbor_det_mk_array ())

[@@pulse_unfold]
let cbor_det_map_entry_match = Impl.cbor_det_map_entry_match

let cbor_det_mk_map_entry = Impl.cbor_det_mk_map_entry

let cbor_det_mk_map_from_array : mk_map_from_array_t cbor_det_match cbor_det_map_entry_match =
  mk_map_from_array (mk_map_from_ref (CBOR.Pulse.API.Det.Type.dummy_cbor_det_t ()) (Impl.cbor_det_mk_map_gen ()))

ghost fn map_gen_post_to_array
  (#t1 #t2: Type0)
  (vmatch1: perm -> t1 -> Spec.cbor -> slprop)
  (vmatch2: perm -> t2 -> (Spec.cbor & Spec.cbor) -> slprop)
  (a: A.array t2)
  (s: S.slice t2)
  (va: (Seq.seq t2))
  (pv: perm)
  (vv: (list (Spec.cbor & Spec.cbor)))
  (vdest0: t1)
  (bres: bool)
  (res: option t1)
  (vdest: t1)
requires
  mk_map_gen_post vmatch1 vmatch2 s va pv vv res **
  S.is_from_array a s **
  pure (mk_map_gen_by_ref_postcond vdest0 res vdest bres)
ensures
  mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest bres
{
  match res {
    None -> {
      unfold (mk_map_gen_post vmatch1 vmatch2 s va pv vv None);
      S.to_array s;
      fold (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest false);
      rewrite (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest false)
        as (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest bres);
    }
    Some vres -> {
      unfold (mk_map_gen_post vmatch1 vmatch2 s va pv vv (Some vres));
      with w va' . assert (Trade.trade (vmatch1 1.0R vres w) (pts_to s va' ** PM.seq_list_match va vv (vmatch2 pv)));
      intro
        (Trade.trade
          (S.pts_to s va')
          (A.pts_to a va')
        )
        #(S.is_from_array a s)
        fn _
      {
        S.to_array s;
      };
      Trade.trans_concl_l _ _ _ _;
      rewrite each vres as vdest;
      fold (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest true);
      rewrite (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest true)
        as (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest bres);
    }
  }
}

fn cbor_det_mk_map_from_array_safe () :
  mk_map_from_array_safe_t #_ #_ cbor_det_match cbor_det_map_entry_match
=
  (a: _)
  (len: _)
  (dest: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  with vdest0 . assert (pts_to dest vdest0);
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  S.pts_to_len s;
  PM.seq_list_match_length (cbor_det_map_entry_match pv) va vv;
  let bres = Impl.cbor_det_mk_map_gen () s dest;
  with res . assert (mk_map_gen_post cbor_det_match cbor_det_map_entry_match s va pv vv res);
  with vdest . assert (pts_to dest vdest);
  map_gen_post_to_array _ _ a s va pv vv vdest0 bres res vdest;
  bres
}

(* ======== Destructors ======== *)

let cbor_det_equal = Impl.cbor_det_equal

let cbor_det_major_type = Impl.cbor_det_major_type

let cbor_det_read_simple_value = Impl.cbor_det_read_simple_value

let cbor_det_elim_simple = Impl.cbor_det_elim_simple

let cbor_det_read_uint64 = Impl.cbor_det_read_uint64

let cbor_det_elim_int64 = Impl.cbor_det_elim_int64

let cbor_det_get_string_length = Impl.cbor_det_get_string_length

let cbor_det_get_tagged_tag = Impl.cbor_det_get_tagged_tag

let cbor_det_get_tagged_payload = Impl.cbor_det_get_tagged_payload

let cbor_det_get_string = Impl.cbor_det_get_string

let cbor_det_get_array_length = Impl.cbor_det_get_array_length

[@@pulse_unfold]
let cbor_det_array_iterator_match = Impl.cbor_det_array_iterator_match

let cbor_det_array_iterator_start = Impl.cbor_det_array_iterator_start
let cbor_det_array_iterator_is_empty = Impl.cbor_det_array_iterator_is_empty
let cbor_det_array_iterator_length = Impl.cbor_det_array_iterator_length
let cbor_det_array_iterator_next = Impl.cbor_det_array_iterator_next
let cbor_det_array_iterator_truncate = Impl.cbor_det_array_iterator_truncate
let cbor_det_array_iterator_share = Impl.cbor_det_array_iterator_share
let cbor_det_array_iterator_gather = Impl.cbor_det_array_iterator_gather

module R = Pulse.Lib.Reference

let rec list_index_cons (#a: Type) (hd: a) (tl: list a) (n: nat)
: Lemma
    (requires n < List.Tot.length tl)
    (ensures
      List.Tot.index (hd :: tl) (n + 1) == List.Tot.index tl n /\
      List.Tot.length (hd :: tl) == 1 + List.Tot.length tl
    )
= ()

#restart-solver
fn cbor_det_get_array_item (_: unit) : get_array_item_t cbor_det_match
= (x: cbor_det_t)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
{
  let orig_list : Ghost.erased (list Spec.cbor) = Ghost.hide (Spec.CArray?.v (Spec.unpack y));
  let it = cbor_det_array_iterator_start () x;
  with p_it l_it . assert (cbor_det_array_iterator_match p_it it l_it);
  let mut pit = it;
  let mut pj = 0uL;
  let cont0 = U64.lt 0uL i;
  let mut pcont = cont0;
  while (
    !pcont
  )
  invariant exists* j_val cont iter suffix piter .
    R.pts_to pj j_val **
    R.pts_to pcont cont **
    R.pts_to pit iter **
    cbor_det_array_iterator_match piter iter suffix **
    Trade.trade (cbor_det_array_iterator_match piter iter suffix) (cbor_det_match p x y) **
    pure (
      U64.v j_val <= U64.v i /\
      List.Tot.length suffix + U64.v j_val == List.Tot.length (Ghost.reveal orig_list) /\
      U64.v i - U64.v j_val < List.Tot.length suffix /\
      List.Tot.index suffix (U64.v i - U64.v j_val) == List.Tot.index (Ghost.reveal orig_list) (U64.v i) /\
      cont == (U64.v j_val < U64.v i)
    )
  {
    with gj gcont gi gsuffix gpiter .
      assert (
        R.pts_to pj gj **
        R.pts_to pcont gcont **
        R.pts_to pit gi **
        cbor_det_array_iterator_match gpiter gi gsuffix **
        Trade.trade (cbor_det_array_iterator_match gpiter gi gsuffix) (cbor_det_match p x y)
      );
    let elem = cbor_det_array_iterator_next () pit;
    with p_elem p_iter' v_elem iter' z_tl .
      assert (
        cbor_det_match p_elem elem v_elem **
        R.pts_to pit iter' **
        cbor_det_array_iterator_match p_iter' iter' z_tl **
        Trade.trade
          (cbor_det_match p_elem elem v_elem ** cbor_det_array_iterator_match p_iter' iter' z_tl)
          (cbor_det_array_iterator_match gpiter gi gsuffix) **
        pure (Ghost.reveal gsuffix == v_elem :: z_tl)
      );
    Trade.elim_hyp_l
      (cbor_det_match p_elem elem v_elem)
      (cbor_det_array_iterator_match p_iter' iter' z_tl)
      (cbor_det_array_iterator_match gpiter gi gsuffix);
    Trade.trans
      (cbor_det_array_iterator_match p_iter' iter' z_tl)
      (cbor_det_array_iterator_match gpiter gi gsuffix)
      (cbor_det_match p x y);
    let j_val = !pj;
    pj := U64.add j_val 1uL;
    let new_cont = U64.lt (U64.add j_val 1uL) i;
    pcont := new_cont;
    ()
  };
  // Now j_val == i, suffix starts at element i
  let res = cbor_det_array_iterator_next () pit;
  with p_res p_iter_final v_res iter_final z_final .
    assert (
      cbor_det_match p_res res v_res **
      R.pts_to pit iter_final **
      cbor_det_array_iterator_match p_iter_final iter_final z_final **
      Trade.trade
        (cbor_det_match p_res res v_res ** cbor_det_array_iterator_match p_iter_final iter_final z_final)
        _
    );
  Trade.elim_hyp_r
    (cbor_det_match p_res res v_res)
    (cbor_det_array_iterator_match p_iter_final iter_final z_final)
    _;
  Trade.trans
    (cbor_det_match p_res res v_res)
    _
    (cbor_det_match p x y);
  res
}

let cbor_det_get_map_length = Impl.cbor_det_get_map_length

(* TODO: full map iterator family — item 10. The array iterator analogue
   from Det.Impl can be mirrored once Access.cbor_raw_get_map is wired in
   here. Marked admits as TODO for now. *)
let cbor_det_map_iterator_match = Impl.cbor_det_map_iterator_match

let cbor_det_map_iterator_start = Impl.cbor_det_map_iterator_start

let cbor_det_map_iterator_is_empty = Impl.cbor_det_map_iterator_is_empty

let cbor_det_map_iterator_next = Impl.cbor_det_map_iterator_next

let cbor_det_map_iterator_share = Impl.cbor_det_map_iterator_share

let cbor_det_map_iterator_gather = Impl.cbor_det_map_iterator_gather

let cbor_det_map_entry_key = Impl.cbor_det_map_entry_key
let cbor_det_map_entry_value = Impl.cbor_det_map_entry_value
let cbor_det_map_entry_share = Impl.cbor_det_map_entry_share
let cbor_det_map_entry_gather = Impl.cbor_det_map_entry_gather

(* ======== map_get helpers ======== *)

let cbor_det_mg_inv_none
  (px: perm) (x: cbor_det_t) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_det_map_iterator_t) (cont: bool)
: Tot slprop
= exists* p_i l .
    cbor_det_map_iterator_match p_i i l **
    Trade.trade
      (cbor_det_map_iterator_match p_i i l)
      (cbor_det_match px x vx) **
    pure (
      Spec.cbor_map_get m vk == (if cont then List.Tot.assoc vk l else None) /\
      (cont ==> Cons? l)
    )

let cbor_det_mg_inv_some
  (px: perm) (x: cbor_det_t) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (x': cbor_det_t)
: Tot slprop
= exists* p' vx' .
    cbor_det_match p' x' vx' **
    Trade.trade
      (cbor_det_match p' x' vx')
      (cbor_det_match px x vx) **
    pure (Spec.cbor_map_get m vk == Some vx')

let cbor_det_mg_inv
  (cont: bool) (px: perm) (x: cbor_det_t) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_det_map_iterator_t) (res: option cbor_det_t)
: Tot slprop
= match res with
  | None -> cbor_det_mg_inv_none px x vx vk m i cont
  | Some x' -> cbor_det_mg_inv_some px x vx vk m x'

ghost
fn cbor_det_mg_inv_false_elim
  (#gb: bool)
  (px: perm) (x: cbor_det_t) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_det_map_iterator_t)
  (res: option cbor_det_t)
requires
  cbor_det_mg_inv gb px x vx vk m i res **
  pure (gb == false /\ Spec.CMap? (Spec.unpack vx) /\ m == Spec.CMap?.c (Spec.unpack vx))
ensures
  map_get_post cbor_det_match x px vx vk res **
  pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
{
  rewrite each gb as false;
  match res {
    None -> {
      unfold (cbor_det_mg_inv false px x vx vk m i None);
      unfold (cbor_det_mg_inv_none px x vx vk m i false);
      Trade.elim _ _;
      fold (map_get_post_none cbor_det_match x px vx vk);
      fold (map_get_post cbor_det_match x px vx vk None);
      rewrite (map_get_post cbor_det_match x px vx vk None)
        as (map_get_post cbor_det_match x px vx vk res);
    }
    Some x' -> {
      unfold (cbor_det_mg_inv false px x vx vk m i (Some x'));
      unfold (cbor_det_mg_inv_some px x vx vk m x');
      fold (map_get_post_some cbor_det_match x px vx vk x');
      fold (map_get_post cbor_det_match x px vx vk (Some x'));
      rewrite (map_get_post cbor_det_match x px vx vk (Some x'))
        as (map_get_post cbor_det_match x px vx vk res);
    }
  }
}

#restart-solver
fn cbor_det_map_get (_: unit) : map_get_by_ref_t cbor_det_match
= (x: cbor_det_t)
  (k: cbor_det_t)
  (dest: R.ref cbor_det_t)
  (#px: perm)
  (#vx: Ghost.erased Spec.cbor)
  (#pk: perm)
  (#vk: Ghost.erased Spec.cbor)
  (#vdest0: Ghost.erased cbor_det_t)
{
  let m : Ghost.erased Spec.cbor_map = Ghost.hide (Spec.CMap?.c (Spec.unpack vx));
  let it = cbor_det_map_iterator_start () x;
  with p_it l_it . assert (cbor_det_map_iterator_match p_it it l_it);
  let mut pit = it;
  let mut pres = None #cbor_det_t;
  let is_empty = cbor_det_map_iterator_is_empty () it;
  let cont0 = not is_empty;
  let mut pcont = cont0;
  fold (cbor_det_mg_inv_none px x vx vk m it cont0);
  fold (cbor_det_mg_inv cont0 px x vx vk m it None);
  while (
    !pcont
  )
  invariant exists* i_val cont res_val .
    R.pts_to pit i_val **
    R.pts_to pcont cont **
    R.pts_to pres res_val **
    cbor_det_match pk k vk **
    R.pts_to dest vdest0 **
    cbor_det_mg_inv cont px x vx vk m i_val res_val **
    pure (cont == true ==> None? res_val)
  {
    with gi gcont gres . assert (cbor_det_mg_inv gcont px x vx vk m gi gres);
    rewrite (cbor_det_mg_inv gcont px x vx vk m gi gres)
      as (cbor_det_mg_inv gcont px x vx vk m gi None);
    unfold (cbor_det_mg_inv gcont px x vx vk m gi None);
    unfold (cbor_det_mg_inv_none px x vx vk m gi gcont);
    let entry = cbor_det_map_iterator_next () pit;
    Trade.trans _ _ (cbor_det_match px x vx);
    with pentry ventry . assert (cbor_det_map_entry_match pentry entry ventry);
    let key = cbor_det_map_entry_key () entry;
    with pk_key . assert (cbor_det_match pk_key key (fst ventry));
    let eq = cbor_det_equal () key k;
    Trade.elim (cbor_det_match pk_key key (fst ventry)) (cbor_det_map_entry_match pentry entry ventry);
    with p_iter' iter' z_tl . assert (cbor_det_map_iterator_match p_iter' iter' z_tl);
    if eq {
      Trade.elim_hyp_r
        (cbor_det_map_entry_match pentry entry ventry)
        (cbor_det_map_iterator_match p_iter' iter' z_tl)
        (cbor_det_match px x vx);
      let value = cbor_det_map_entry_value () entry;
      Trade.trans _ _ (cbor_det_match px x vx);
      pres := Some value;
      pcont := false;
      fold (cbor_det_mg_inv_some px x vx vk m value);
      fold (cbor_det_mg_inv false px x vx vk m iter' (Some value))
    } else {
      Trade.elim_hyp_l
        (cbor_det_map_entry_match pentry entry ventry)
        (cbor_det_map_iterator_match p_iter' iter' z_tl)
        (cbor_det_match px x vx);
      let i' = !pit;
      Trade.rewrite_with_trade
        (cbor_det_map_iterator_match p_iter' iter' z_tl)
        (cbor_det_map_iterator_match p_iter' i' z_tl);
      Trade.trans _ _ (cbor_det_match px x vx);
      let is_empty' = cbor_det_map_iterator_is_empty () i';
      let cont' = not is_empty';
      pcont := cont';
      fold (cbor_det_mg_inv_none px x vx vk m i' cont');
      assert (R.pts_to pres None);
      fold (cbor_det_mg_inv cont' px x vx vk m i' None)
    }
  };
  with gi gcont gres . assert (cbor_det_mg_inv gcont px x vx vk m gi gres);
  cbor_det_mg_inv_false_elim px x vx vk m gi gres;
  let res = !pres;
  match res {
    None -> {
      false
    }
    Some vres -> {
      dest := vres;
      true
    }
  }
}

(* ======== Serializer wrappers (slice → ArrayPtr) ======== *)

fn cbor_det_serialize_tag_to_array (_: unit)
: cbor_det_serialize_tag_to_array_t
=
  (tag: _)
  (out: _)
  (out_len: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_tag () tag sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_array_to_array (_: unit)
: cbor_det_serialize_array_to_array_t
=
  (len: _)
  (out: _)
  (out_len: _)
  (l: _)
  (off: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_array () len sout l off;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_string_to_array (_: unit)
: cbor_det_serialize_string_to_array_t
=
  (ty: _)
  (off: _)
  (out: _)
  (out_len: _)
  (#v: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_string () ty off sout;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_map_insert_to_array (_: unit)
: cbor_det_serialize_map_insert_to_array_t
=
  (out: _)
  (out_len: _)
  (m: _)
  (off2: _)
  (key: _)
  (off3: _)
  (value: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_map_insert () sout m off2 key off3 value;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_map_to_array (_: unit)
: cbor_det_serialize_map_to_array_t
=
  (len: _)
  (out: _)
  (out_len: _)
  (l: _)
  (off: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_map () len sout l off;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}
