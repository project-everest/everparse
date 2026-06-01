module CBOR.Pulse.API.Det.Rust
#lang-pulse

(* Implementation of CBOR.Pulse.API.Det.Rust.fsti using the new
   EverParse-based stack (CBOR.Pulse.Raw.EverParse.Det.Impl). *)

module Impl = CBOR.Pulse.Raw.EverParse.Det.Impl
module SU = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module PM = Pulse.Lib.SeqMatch
module UTF8 = CBOR.Pulse.API.UTF8

open CBOR.Spec.Constants
open CBOR.Pulse.API.Base

(* ======== Types and match relation ======== *)

type cbordet = CBOR.Pulse.API.Det.Type.cbor_det_t

[@@pulse_unfold]
let cbor_det_match = Impl.cbor_det_match

let cbor_det_reset_perm () = Impl.cbor_det_reset_perm ()

let cbor_det_share () = Impl.cbor_det_share ()
let cbor_det_gather () = Impl.cbor_det_gather ()

(* ======== Validate, parse, size, serialize ======== *)

let cbor_det_parse () =
  cbor_det_parse_full (Impl.cbor_det_validate ()) (Impl.cbor_det_parse_valid ())

fn cbor_det_size
  (x: cbordet)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (cbor_det_match pm x y)
returns res: option SZ.t
ensures
  cbor_det_match pm x y **
  pure (cbor_det_size_postcond y bound res)
{
  let size = Impl.cbor_det_size x bound;
  if (size = 0sz) {
    None #SZ.t
  } else {
    Some size
  }
}

fn cbor_det_serialize
  (_: unit)
: Base.cbor_det_serialize_t u#0 #_ cbor_det_match
=
  (x: cbordet)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len output;
  let size = Impl.cbor_det_size x (S.len output);
  if (SZ.gt size 0sz) {
    let out, rem = S.split output size;
    S.pts_to_len out;
    Impl.cbor_det_serialize_slice x out;
    S.pts_to_len out;
    with v1 . assert (S.pts_to out v1);
    assert (pure (Seq.equal v1 (Spec.cbor_det_serialize y)));
    S.join out rem output;
    with v' . assert (S.pts_to output v');
    Seq.lemma_split v' (SZ.v size);
    assert (pure (Seq.equal (Seq.slice v' 0 (SZ.v size)) (Spec.cbor_det_serialize y)));
    assert (pure (Seq.equal (Seq.slice v' (SZ.v size) (Seq.length v)) (Seq.slice v (SZ.v size) (Seq.length v))));
    Some size
  } else {
    None #SZ.t
  }
}

(* ======== Constructors ======== *)

fn cbor_det_mk_simple_value
  (v: U8.t)
requires emp
returns res: option cbordet
ensures
  cbor_det_mk_simple_value_post v res **
  pure (Some? res <==> simple_value_wf v)
{
  if simple_value_wf v {
    let res = Impl.cbor_det_mk_simple_value () v;
    fold (cbor_det_mk_simple_value_post v (Some res));
    Some res
  }
  else {
    fold (cbor_det_mk_simple_value_post v None);
    None #cbordet
  }
}

fn cbor_det_mk_int64
  (ty: cbor_det_int_kind)
  (v: U64.t)
requires emp
returns res: cbordet
ensures cbor_det_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v))
{
  Impl.cbor_det_mk_int64 () (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v
}

let uint64_max_prop : squash (pow2 64 - 1 == 18446744073709551615) =
  assert_norm (pow2 64 - 1 == 18446744073709551615)

fn cbor_impl_utf8_correct () : Base.impl_utf8_correct_t =
  (s: _)
  (#p: _)
  (#v: _)
{
  UTF8.impl_utf8_correct s
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_string_is_correct
  (ty: cbor_det_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to s #p v
returns res: bool
ensures 
  pts_to s #p v **
  pure (res == true <==> (ty == TextString ==> CBOR.Spec.API.UTF8.correct v))
{
  if (ty = TextString) {
    cbor_impl_utf8_correct () s
  } else {
    true
  }
}

fn cbor_det_mk_string
  (ty: cbor_det_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to s #p v
returns res: option cbordet
ensures
  cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v res **
  pure (Some? res <==> (FStar.UInt.fits (SZ.v (S.len s)) U64.n /\ (ty == TextString ==> CBOR.Spec.API.UTF8.correct v)))
{
  let sq: squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  if SZ.gt (S.len s) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
    None #cbordet
  } else {
    let correct = cbor_det_mk_string_is_correct ty s;
    if correct {
      let res = Impl.cbor_det_mk_string () (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s;
      fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v (Some res));
      Some res
    } else {
      fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
      None #cbordet
    }
  }
}

let cbor_det_mk_tagged tag r #pr #v #pv #v' = Impl.cbor_det_mk_tagged () tag r #pr #v #pv #v'

(* ======== Map entry ======== *)

let cbor_det_map_entry = CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t

[@@pulse_unfold]
let cbor_det_map_entry_match = Impl.cbor_det_map_entry_match

let cbor_det_mk_map_entry xk xv #pk #vk #pv #vv = Impl.cbor_det_mk_map_entry () xk xv #pk #vk #pv #vv

(* ======== mk_array ======== *)

fn cbor_det_mk_array
  (a: S.slice cbordet)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbordet))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
requires
    pts_to a #pa va **
    PM.seq_list_match va vv (cbor_det_match pv)
returns res: option cbordet
ensures
  cbor_det_mk_array_post a pa va pv vv res **
  pure (Some? res <==> FStar.UInt.fits (SZ.v (S.len a)) U64.n)
{
  let _ : squash SZ.fits_u64 = assume (SZ.fits_u64);
  if SZ.gt (S.len a) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_det_mk_array_post a pa va pv vv None);
    None #cbordet;
  } else {
    let res = Impl.cbor_det_mk_array () a;
    fold (cbor_det_mk_array_post a pa va pv vv (Some res));
    Some res
  }
}

(* ======== mk_map ======== *)

let cbor_det_mk_map (_: unit) : Base.mk_map_gen_t u#0 #_ #_ cbor_det_match cbor_det_map_entry_match
= Base.mk_map_gen (CBOR.Pulse.API.Det.Dummy.dummy_cbor_det_t ()) (Impl.cbor_det_mk_map_gen ())

(* ======== Destructors ======== *)

let cbor_det_equal x1 x2 #p1 #p2 #v1 #v2 = Impl.cbor_det_equal () x1 x2 #p1 #p2 #v1 #v2

let cbor_det_major_type _ x #p #v = Impl.cbor_det_major_type () x #p #v

(* ======== Array and Map wrapper types ======== *)

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_det_array = {
  array: cbordet;
}

let cbor_det_array_match (p: perm) (a: cbor_det_array) (v: Spec.cbor) : Tot slprop =
  cbor_det_match p a.array v **
  pure (Spec.CArray? (Spec.unpack v))

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_det_map = {
  map: cbordet;
}

noextract [@@noextract_to "krml"]
let cbor_det_map_match (p: perm) (a: cbor_det_map) (v: Spec.cbor) : Tot slprop =
  cbor_det_match p a.map v **
  pure (Spec.CMap? (Spec.unpack v))

(* ======== cbor_det_destruct ======== *)

#push-options "--z3rlimit 64"

fn cbor_det_destruct
  (c: cbordet)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
requires
  cbor_det_match p c v
returns w: cbor_det_view
ensures exists* p' .
  cbor_det_view_match p' w v **
  Trade.trade
    (cbor_det_view_match p' w v)
    (cbor_det_match p c v) **
  pure (cbor_det_destruct_postcond w v)
{
  let ty = Impl.cbor_det_major_type () c;
  if (ty = cbor_major_type_uint64 || ty = cbor_major_type_neg_int64) {
    let k = (if ty = cbor_major_type_uint64 then UInt64 else NegInt64);
    let i = Impl.cbor_det_read_uint64 () c;
    fold (cbor_det_view_match p (Int64 k i) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (Int64 k i) v)
        (cbor_det_match p c v)
      )
      #(cbor_det_match p c v)
      fn _
    {
      unfold (cbor_det_view_match p (Int64 k i) v)
    };
    Int64 k i
  }
  else if (ty = cbor_major_type_byte_string || ty = cbor_major_type_text_string) {
    let k = (if ty = cbor_major_type_byte_string then ByteString else TextString);
    let sl = Impl.cbor_det_get_string_slice () c;
    with p_sl v_sl . assert (S.pts_to sl #p_sl v_sl);
    fold (cbor_det_string_match ty p_sl sl v);
    rewrite (cbor_det_string_match ty p_sl sl v) as (cbor_det_view_match p_sl (String k sl) v);
    intro
      (Trade.trade
        (cbor_det_view_match p_sl (String k sl) v)
        (S.pts_to sl #p_sl v_sl)
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p_sl (String k sl) v);
      with ty' . unfold (cbor_det_string_match ty' p_sl sl v);
    };
    Trade.trans _ _ (cbor_det_match p c v);
    String k sl
  }
  else if (ty = cbor_major_type_array) {
    let res : cbor_det_array = { array = c };
    rewrite cbor_det_match p c v as cbor_det_match p res.array v;
    fold (cbor_det_array_match p res v);
    fold (cbor_det_view_match p (Array res) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (Array res) v)
        (cbor_det_match p c v)
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p (Array res) v);
      unfold (cbor_det_array_match p res v);
      rewrite cbor_det_match p res.array v as cbor_det_match p c v;
    };
    Array res
  }
  else if (ty = cbor_major_type_map) {
    let res : cbor_det_map = { map = c };
    rewrite cbor_det_match p c v as cbor_det_match p res.map v;
    fold (cbor_det_map_match p res v);
    fold (cbor_det_view_match p (Map res) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (Map res) v)
        (cbor_det_match p c v)
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p (Map res) v);
      unfold (cbor_det_map_match p res v);
      rewrite cbor_det_match p res.map v as cbor_det_match p c v;
    };
    Map res
  }
  else if (ty = cbor_major_type_tagged) {
    let tag = Impl.cbor_det_get_tagged_tag () c;
    let payload = Impl.cbor_det_get_tagged_payload () c;
    with p' v' . assert (cbor_det_match p' payload v');
    fold (cbor_det_tagged_match p' tag payload v);
    fold (cbor_det_view_match p' (Tagged tag payload) v);
    intro
      (Trade.trade
        (cbor_det_view_match p' (Tagged tag payload) v)
        (cbor_det_match p' payload v')
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p' (Tagged tag payload) v);
      unfold (cbor_det_tagged_match p' tag payload v);
      with v_ . rewrite cbor_det_match p' payload v_ as cbor_det_match p' payload v'
    };
    Trade.trans _ _ (cbor_det_match p c v);
    Tagged tag payload
  }
  else {
    let i = Impl.cbor_det_read_simple_value () c;
    fold (cbor_det_view_match p (SimpleValue i) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (SimpleValue i) v)
        (cbor_det_match p c v)
      )
      #(cbor_det_match p c v)
      fn _
    {
      unfold (cbor_det_view_match p (SimpleValue i) v)
    };
    SimpleValue i
  }
}

#pop-options

(* ======== elim_int64, elim_simple_value ======== *)

let cbor_det_elim_int64 () = Impl.cbor_det_elim_int64 ()

let cbor_det_elim_simple_value () = Impl.cbor_det_elim_simple ()

(* ======== Array: get_array_length ======== *)

ghost
fn cbor_det_array_match_elim
  (x: cbor_det_array)
  (#p: perm)
  (#y: Spec.cbor)
requires cbor_det_array_match p x y
ensures cbor_det_match p x.array y **
  Trade.trade (cbor_det_match p x.array y) (cbor_det_array_match p x y) **
  pure (Spec.CArray? (Spec.unpack y))
{
  unfold (cbor_det_array_match p x y);
  intro
    (Trade.trade
      (cbor_det_match p x.array y)
      (cbor_det_array_match p x y)
    )
    #emp
    fn _
  {
    fold (cbor_det_array_match p x y);
  };
}

fn cbor_det_get_array_length
  (x: cbor_det_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_array_match p x y
returns res: U64.t
ensures
  cbor_det_array_match p x y ** pure (
    get_array_length_post y res
  )
{
  unfold (cbor_det_array_match p x y);
  let res = Impl.cbor_det_get_array_length () x.array;
  fold (cbor_det_array_match p x y);
  res
}

(* ======== Array iterator ======== *)

let cbor_det_array_iterator_t = CBOR.Pulse.API.Det.Type.cbor_det_array_iterator_t

[@@pulse_unfold]
let cbor_det_array_iterator_match = Impl.cbor_det_array_iterator_match

fn cbor_det_array_iterator_start
  (x: cbor_det_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  (cbor_det_array_match p x y)
returns res: cbor_det_array_iterator_t
ensures
    (exists* p' l' .
      cbor_det_array_iterator_match p' res l' **
      Trade.trade
        (cbor_det_array_iterator_match p' res l')
        (cbor_det_array_match p x y) **
      pure (
        Spec.CArray? (Spec.unpack y) /\
        l' == Spec.CArray?.v (Spec.unpack y)
    ))
{
  cbor_det_array_match_elim x;
  let res = Impl.cbor_det_array_iterator_start () x.array;
  Trade.trans _ _ (cbor_det_array_match p x y);
  res
}

let cbor_det_array_iterator_is_empty x #p #y = Impl.cbor_det_array_iterator_is_empty () x #p #y

let cbor_det_array_iterator_next = Base.array_iterator_next_by_value (Impl.cbor_det_array_iterator_next ())

let cbor_det_array_iterator_share = Impl.cbor_det_array_iterator_share ()

let cbor_det_array_iterator_gather = Impl.cbor_det_array_iterator_gather ()

let cbor_det_array_iterator_length = Impl.cbor_det_array_iterator_length ()

let cbor_det_array_iterator_truncate = Impl.cbor_det_array_iterator_truncate ()

(* ======== cbor_det_get_array_item ======== *)

let rec list_index_cons (#a: Type) (hd: a) (tl: list a) (n: nat)
: Lemma
    (requires n < List.Tot.length tl)
    (ensures
      List.Tot.index (hd :: tl) (n + 1) == List.Tot.index tl n /\
      List.Tot.length (hd :: tl) == 1 + List.Tot.length tl
    )
= ()

#push-options "--z3rlimit 64"

fn cbor_det_get_array_item
  (x: cbor_det_array)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_array_match p x y
returns res: option cbordet
ensures
  safe_get_array_item_post x i p y res **
  pure (cbor_det_get_array_item_postcond i y res)
{
  let len = cbor_det_get_array_length x;
  if U64.gte i len {
    fold (safe_get_array_item_post x i p y None);
    None #cbordet
  } else {
    cbor_det_array_match_elim x;
    let orig_list : Ghost.erased (list Spec.cbor) = Ghost.hide (Spec.CArray?.v (Spec.unpack y));
    let it = Impl.cbor_det_array_iterator_start () x.array;
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
      Trade.trade (cbor_det_array_iterator_match piter iter suffix) (cbor_det_match p x.array y) **
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
          Trade.trade (cbor_det_array_iterator_match gpiter gi gsuffix) (cbor_det_match p x.array y)
        );
      let elem = Impl.cbor_det_array_iterator_next () pit;
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
        (cbor_det_match p x.array y);
      let j_val = !pj;
      pj := U64.add j_val 1uL;
      let new_cont = U64.lt (U64.add j_val 1uL) i;
      pcont := new_cont;
      ()
    };
    // Now j_val == i, suffix starts at element i
    let res = Impl.cbor_det_array_iterator_next () pit;
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
      (cbor_det_match p x.array y);
    Trade.trans
      (cbor_det_match p_res res v_res)
      (cbor_det_match p x.array y)
      (cbor_det_array_match p x y);
    fold (safe_get_array_item_post x i p y (Some res));
    Some res
  }
}

#pop-options

(* ======== Map: length ======== *)

fn cbor_det_map_length
  (x: cbor_det_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_map_match p x y
returns res: U64.t
ensures
  cbor_det_map_match p x y ** pure (
    get_map_length_post y res
  )
{
  unfold (cbor_det_map_match p x y);
  let res = Impl.cbor_det_get_map_length () x.map;
  fold (cbor_det_map_match p x y);
  res
}

(* ======== Map iterator ======== *)

ghost
fn cbor_det_map_match_elim
  (x: cbor_det_map)
  (#p: perm)
  (#y: Spec.cbor)
requires cbor_det_map_match p x y
ensures cbor_det_match p x.map y **
  Trade.trade (cbor_det_match p x.map y) (cbor_det_map_match p x y) **
  pure (Spec.CMap? (Spec.unpack y))
{
  unfold (cbor_det_map_match p x y);
  intro
    (Trade.trade
      (cbor_det_match p x.map y)
      (cbor_det_map_match p x y)
    )
    #emp
    fn _
  {
    fold (cbor_det_map_match p x y);
  };
}

let cbor_det_map_iterator_t = CBOR.Pulse.API.Det.Type.cbor_det_map_iterator_t

[@@pulse_unfold]
let cbor_det_map_iterator_match = Impl.cbor_det_map_iterator_match

fn cbor_det_map_iterator_start
  (x: cbor_det_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  (cbor_det_map_match p x y)
returns res: cbor_det_map_iterator_t
ensures
    (exists* p' l' .
      cbor_det_map_iterator_match p' res l' **
      Trade.trade
        (cbor_det_map_iterator_match p' res l')
        (cbor_det_map_match p x y) **
      pure (
        map_iterator_start_post y l'
    ))
{
  cbor_det_map_match_elim x;
  let res = Impl.cbor_det_map_iterator_start () x.map;
  Trade.trans _ _ (cbor_det_map_match p x y);
  res
}

let cbor_det_map_iterator_is_empty x #p #y = Impl.cbor_det_map_iterator_is_empty () x #p #y

let cbor_det_map_iterator_next = Base.map_iterator_next_by_value (Impl.cbor_det_map_iterator_next ())

let cbor_det_map_iterator_share = Impl.cbor_det_map_iterator_share ()

let cbor_det_map_iterator_gather = Impl.cbor_det_map_iterator_gather ()

(* ======== Map entry ======== *)

let cbor_det_map_entry_key x2 #p #v2 = Impl.cbor_det_map_entry_key () x2 #p #v2

let cbor_det_map_entry_value x2 #p #v2 = Impl.cbor_det_map_entry_value () x2 #p #v2

let cbor_det_map_entry_share = Impl.cbor_det_map_entry_share ()

let cbor_det_map_entry_gather = Impl.cbor_det_map_entry_gather ()

(* ======== cbor_det_map_get ======== *)

ghost
fn cbor_det_map_get_post_to_safe
  (x: cbor_det_map)
  (px: perm)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (res: option cbordet)
requires
  pure (Spec.CMap? (Spec.unpack vx) /\ Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res) **
  map_get_post cbor_det_match x.map px vx vk res **
  Trade.trade (cbor_det_match px x.map vx) (cbor_det_map_match px x vx)
ensures
  safe_map_get_post x px vx vk res
{
  match res {
    None -> {
      unfold (map_get_post cbor_det_match x.map px vx vk None);
      unfold (map_get_post_none cbor_det_match x.map px vx vk);
      Trade.elim _ _;
      fold (safe_map_get_post x px vx vk None);
      rewrite (safe_map_get_post x px vx vk None) as (safe_map_get_post x px vx vk res)
    }
    Some res' -> {
      unfold (map_get_post cbor_det_match x.map px vx vk (Some res'));
      unfold (map_get_post_some cbor_det_match x.map px vx vk res');
      Trade.trans _ _ (cbor_det_map_match px x vx);
      fold (safe_map_get_post x px vx vk (Some res'));
      rewrite (safe_map_get_post x px vx vk (Some res')) as (safe_map_get_post x px vx vk res)
    }
  }
}

(* The map_get loop uses the map_get_by_ref_t from Det.C as a template *)

let cbor_det_mg_inv_none
  (px: perm) (x: cbordet) (vx: Spec.cbor) (vk: Spec.cbor)
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
  (px: perm) (x: cbordet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (x': cbordet)
: Tot slprop
= exists* p' vx' .
    cbor_det_match p' x' vx' **
    Trade.trade
      (cbor_det_match p' x' vx')
      (cbor_det_match px x vx) **
    pure (Spec.cbor_map_get m vk == Some vx')

let cbor_det_mg_inv
  (cont: bool) (px: perm) (x: cbordet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_det_map_iterator_t) (res: option cbordet)
: Tot slprop
= match res with
  | None -> cbor_det_mg_inv_none px x vx vk m i cont
  | Some x' -> cbor_det_mg_inv_some px x vx vk m x'

ghost
fn cbor_det_mg_inv_false_elim
  (#gb: bool)
  (px: perm) (x: cbordet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_det_map_iterator_t)
  (res: option cbordet)
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

#push-options "--z3rlimit 64"

fn cbor_det_map_get
  (x: cbor_det_map)
  (k: cbordet)
  (#px: perm)
  (#vx: Ghost.erased Spec.cbor)
  (#pk: perm)
  (#vk: Ghost.erased Spec.cbor)
requires
    (cbor_det_map_match px x vx ** cbor_det_match pk k vk)
returns res: option cbordet
ensures
    (
      cbor_det_match pk k vk **
      safe_map_get_post x px vx vk res **
      pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
    )
{
  cbor_det_map_match_elim x;
  let m : Ghost.erased Spec.cbor_map = Ghost.hide (Spec.CMap?.c (Spec.unpack vx));
  let it = Impl.cbor_det_map_iterator_start () x.map;
  with p_it l_it . assert (cbor_det_map_iterator_match p_it it l_it);
  let mut pit = it;
  let mut pres = None #cbordet;
  let is_empty = Impl.cbor_det_map_iterator_is_empty () it;
  let cont0 = not is_empty;
  let mut pcont = cont0;
  fold (cbor_det_mg_inv_none px x.map vx vk m it cont0);
  fold (cbor_det_mg_inv cont0 px x.map vx vk m it None);
  while (
    !pcont
  )
  invariant exists* i_val cont res_val .
    R.pts_to pit i_val **
    R.pts_to pcont cont **
    R.pts_to pres res_val **
    cbor_det_match pk k vk **
    cbor_det_mg_inv cont px x.map vx vk m i_val res_val **
    pure (cont == true ==> None? res_val)
  {
    with gi gcont gres . assert (cbor_det_mg_inv gcont px x.map vx vk m gi gres);
    rewrite (cbor_det_mg_inv gcont px x.map vx vk m gi gres)
      as (cbor_det_mg_inv gcont px x.map vx vk m gi None);
    unfold (cbor_det_mg_inv gcont px x.map vx vk m gi None);
    unfold (cbor_det_mg_inv_none px x.map vx vk m gi gcont);
    let entry = Impl.cbor_det_map_iterator_next () pit;
    Trade.trans _ _ (cbor_det_match px x.map vx);
    with pentry ventry . assert (cbor_det_map_entry_match pentry entry ventry);
    let key = Impl.cbor_det_map_entry_key () entry;
    with pk_key . assert (cbor_det_match pk_key key (fst ventry));
    let eq = Impl.cbor_det_equal () key k;
    Trade.elim (cbor_det_match pk_key key (fst ventry)) (cbor_det_map_entry_match pentry entry ventry);
    with p_iter' iter' z_tl . assert (cbor_det_map_iterator_match p_iter' iter' z_tl);
    if eq {
      Trade.elim_hyp_r
        (cbor_det_map_entry_match pentry entry ventry)
        (cbor_det_map_iterator_match p_iter' iter' z_tl)
        (cbor_det_match px x.map vx);
      let value = Impl.cbor_det_map_entry_value () entry;
      Trade.trans _ _ (cbor_det_match px x.map vx);
      pres := Some value;
      pcont := false;
      fold (cbor_det_mg_inv_some px x.map vx vk m value);
      fold (cbor_det_mg_inv false px x.map vx vk m iter' (Some value))
    } else {
      Trade.elim_hyp_l
        (cbor_det_map_entry_match pentry entry ventry)
        (cbor_det_map_iterator_match p_iter' iter' z_tl)
        (cbor_det_match px x.map vx);
      let i' = !pit;
      Trade.rewrite_with_trade
        (cbor_det_map_iterator_match p_iter' iter' z_tl)
        (cbor_det_map_iterator_match p_iter' i' z_tl);
      Trade.trans _ _ (cbor_det_match px x.map vx);
      let is_empty' = Impl.cbor_det_map_iterator_is_empty () i';
      let cont' = not is_empty';
      pcont := cont';
      fold (cbor_det_mg_inv_none px x.map vx vk m i' cont');
      assert (R.pts_to pres None);
      fold (cbor_det_mg_inv cont' px x.map vx vk m i' None)
    }
  };
  with gi gcont gres . assert (cbor_det_mg_inv gcont px x.map vx vk m gi gres);
  cbor_det_mg_inv_false_elim px x.map vx vk m gi gres;
  cbor_det_map_get_post_to_safe x px vx vk gres;
  let res = !pres;
  rewrite (safe_map_get_post x px vx vk gres) as (safe_map_get_post x px vx vk res);
  res
}

#pop-options

(* ======== Serializer wrappers ======== *)

let cbor_det_serialize_string = Impl.cbor_det_serialize_string ()
let cbor_det_serialize_tag = Impl.cbor_det_serialize_tag ()
let cbor_det_serialize_array = Impl.cbor_det_serialize_array ()
let cbor_det_serialize_map_insert = Impl.cbor_det_serialize_map_insert ()
let cbor_det_serialize_map = Impl.cbor_det_serialize_map ()

(* ======== dummy ======== *)

let dummy_cbor_det_t () = CBOR.Pulse.API.Det.Dummy.dummy_cbor_det_t ()
