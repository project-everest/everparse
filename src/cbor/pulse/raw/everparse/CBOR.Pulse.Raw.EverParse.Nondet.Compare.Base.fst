module CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Iterator
open LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen
module Valid = CBOR.Spec.Raw.Valid
module VCList = LowParse.Spec.VCList

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

let cbor_raw_match_fields_prop_of_header x y h _ _ = ()

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_fields
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y
ensures cbor_raw_match pm x y ** pure (cbor_raw_match_fields_prop x y)
{
  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  cbor_raw_match_fields_prop_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  cbor_raw_match_fold_aux x;
  ()
}
```

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_aux_fields
  (r: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match_aux parse_raw_data_item r pm x y
ensures cbor_raw_match_aux parse_raw_data_item r pm x y ** pure (cbor_raw_match_fields_prop x y)
{
  unfold (cbor_raw_match_aux parse_raw_data_item r pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content r parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content r parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  cbor_raw_match_fields_prop_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content r parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content r parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item r pm x (Ghost.reveal y));
}
```

#pop-options

#push-options "--z3rlimit 512 --fuel 4 --ifuel 2"

let rec check_equiv_list_decompose
  (l1 l2: list raw_data_item)
  (q1: list raw_data_item)
  (q2: list raw_data_item)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
: Lemma
  (requires
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.length q1 == List.Tot.length q2 /\
    list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 + list_sum raw_data_item_size q1 + list_sum raw_data_item_size q2 <= bound /\
    list_sum raw_data_item_size (List.Tot.append l1 q1) + list_sum raw_data_item_size (List.Tot.append l2 q2) <= bound)
  (ensures
    check_equiv_list (List.Tot.append l1 q1) (List.Tot.append l2 q2) equiv ==
    option_and (check_equiv_list l1 l2 equiv) (check_equiv_list q1 q2 equiv))
  (decreases (list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2))
= list_sum_append raw_data_item_size l1 q1;
  list_sum_append raw_data_item_size l2 q2;
  List.Tot.Properties.append_length l1 q1;
  List.Tot.Properties.append_length l2 q2;
  match l1, l2 with
  | [], [] ->
    List.Tot.Properties.append_l_nil q1;
    List.Tot.Properties.append_l_nil q2
  | a1 :: r1, a2 :: r2 ->
    raw_data_item_size_eq a1;
    raw_data_item_size_eq a2;
    list_sum_append raw_data_item_size r1 q1;
    list_sum_append raw_data_item_size r2 q2;
    List.Tot.Properties.append_length r1 q1;
    List.Tot.Properties.append_length r2 q2;
    check_equiv_list_decompose r1 r2 q1 q2 bound equiv;
    match equiv a1 a2 with
    | None -> ()
    | Some b ->
      if b then ()
      else match a1, a2 with
      | Tagged tag1 b1, Tagged tag2 b2 ->
        if tag1.value <> tag2.value then ()
        else
          check_equiv_list_decompose (b1 :: r1) (b2 :: r2) q1 q2 bound equiv
      | Array len1 ar1, Array len2 ar2 ->
        if len1.value <> len2.value then ()
        else begin
          List.Tot.Properties.append_assoc ar1 r1 q1;
          List.Tot.Properties.append_assoc ar2 r2 q2;
          List.Tot.Properties.append_length ar1 r1;
          List.Tot.Properties.append_length ar2 r2;
          list_sum_append raw_data_item_size ar1 r1;
          list_sum_append raw_data_item_size ar2 r2;
          list_sum_append raw_data_item_size (List.Tot.append ar1 r1) q1;
          list_sum_append raw_data_item_size (List.Tot.append ar2 r2) q2;
          check_equiv_list_decompose (List.Tot.append ar1 r1) (List.Tot.append ar2 r2) q1 q2 bound equiv
        end
      | _ -> ()

#pop-options

// Wrapper: convert impl_data_model_t (cbor_raw level) to impl_equiv_hd_t (serialized nlist level)
inline_for_extraction
```pulse
fn impl_data_model_to_equiv_hd
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
: NG.impl_equiv_hd_t data_model
=
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (VCList.nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (VCList.nlist (SZ.v n2) raw_data_item))
{
  let hd1 = nlist_hd_strong_prefix () jump_raw_data_item_eta (SZ.v n1) l1;
  let x1 = cbor_raw_read 1.0R f64 hd1;
  Trade.trans _ _
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1);
  let hd2 = nlist_hd_strong_prefix () jump_raw_data_item_eta (SZ.v n2) l2;
  let x2 = cbor_raw_read 1.0R f64 hd2;
  Trade.trans _ _
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2);
  let res = impl_dm x1 x2;
  Trade.elim _ (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2);
  Trade.elim _ (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1);
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn cbor_nondet_impl_basic_local
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2
returns res: bool
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (res == basic_data_model v1 v2)
{
  false
}
```

inline_for_extraction
```pulse
fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (ih: NG.impl_check_equiv_map_hd_t data_model)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (VCList.nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (VCList.nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
requires
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2
returns res: option bool
ensures
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2 **
  pure (
    res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv data_model None) (check_equiv data_model None) gl1) gl2
  )
{
  NG.impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow (impl_check_equiv_compare impl_dm f64 ih None) nl1 l1 nl2 l2
}
```

```pulse
fn rec impl_check_equiv_map_hd_basic
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (VCList.nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (VCList.nlist (SZ.v n2) raw_data_item))
requires
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
  pure (
    SZ.v n1 > 0 /\ SZ.v n2 > 0
  )
returns res: option bool
ensures
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
  pure (
    SZ.v n1 > 0 /\ SZ.v n2 > 0 /\
    res == (check_equiv_map basic_data_model (NG.option_sz_v map_bound)) (List.Tot.hd gl1) (List.Tot.hd gl2)
  )
{
  impl_check_equiv_map_hd_compare cbor_nondet_impl_basic_local f64 (impl_check_equiv_map_hd_basic f64) map_bound n1 l1 n2 l2
}
```

let rec setoid_assoc_eq_with_overflow_check_equiv_ext
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (bound: nat)
  (ll: list (raw_data_item & raw_data_item))
  (xr: (raw_data_item & raw_data_item))
: Lemma
  (requires
    list_sum (pair_sum raw_data_item_size raw_data_item_size) ll +
    pair_sum raw_data_item_size raw_data_item_size xr <= bound)
  (ensures
    setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) ll xr ==
    setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) ll xr)
  (decreases ll)
= match ll with
  | [] -> ()
  | (kl, vl) :: ll' ->
    check_equiv_check_equiv_aux_eq dm mb bound (fst xr) kl;
    match check_equiv dm mb (fst xr) kl with
    | None -> ()
    | Some false ->
      setoid_assoc_eq_with_overflow_check_equiv_ext dm mb bound ll' xr
    | Some true ->
      check_equiv_check_equiv_aux_eq dm mb bound (snd xr) vl

let rec list_for_all_with_overflow_ext
  (#t: Type)
  (f g: t -> option bool)
  (l: list t)
: Lemma
  (requires forall x . List.Tot.memP x l ==> f x == g x)
  (ensures list_for_all_with_overflow f l == list_for_all_with_overflow g l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    assert (f a == g a);
    match f a with
    | Some true -> list_for_all_with_overflow_ext f g q
    | _ -> ()

let check_equiv_map_list_for_all_ext
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (bound: nat)
  (inner outer: list (raw_data_item & raw_data_item))
= let ext_assoc (xr: (raw_data_item & raw_data_item)) : Lemma
    (requires List.Tot.memP xr outer)
    (ensures
      setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) inner xr ==
      setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) inner xr)
  = list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) outer xr;
    setoid_assoc_eq_with_overflow_check_equiv_ext dm mb bound inner xr
  in
  Classical.forall_intro (Classical.move_requires ext_assoc);
  list_for_all_with_overflow_ext
    (setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) inner)
    (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) inner)
    outer

module I16 = FStar.Int16
module Spec = CBOR.Spec.API.Format
module CompareBytes = CBOR.Pulse.Raw.Compare.Bytes

// Coerce Pulse ghost fn to stt_ghost for share_t / gather_t
```pulse
ghost
fn cbor_raw_match_share_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_raw_match p x1 x2
ensures cbor_raw_match (p /. 2.0R) x1 x2 ** cbor_raw_match (p /. 2.0R) x1 x2
{
  cbor_raw_match_share x1
}
```

```pulse
ghost
fn cbor_raw_match_gather_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_raw_match p x1 x2 ** cbor_raw_match p' x1 x2'
ensures cbor_raw_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  cbor_raw_match_gather x1 #p #x2 #p' #x2'
}
```

// Share wrapper for map entry vmatch
```pulse
ghost
fn cbor_map_entry_vmatch_share_wrapper
  (entry: cbor_map_entry cbor_raw) (#pm: perm) (#pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair
ensures cbor_map_entry_vmatch (pm /. 2.0R) entry pair ** cbor_map_entry_vmatch (pm /. 2.0R) entry pair
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  cbor_map_entry_match_share cbor_raw_match cbor_raw_match_share_t entry;
  fold (cbor_map_entry_vmatch (pm /. 2.0R) entry pair);
  fold (cbor_map_entry_vmatch (pm /. 2.0R) entry pair);
}
```

// Gather wrapper for map entry vmatch
```pulse
ghost
fn cbor_map_entry_vmatch_gather_wrapper
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm) (#pair: (raw_data_item & raw_data_item))
  (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair ** cbor_map_entry_vmatch pm' entry pair'
ensures cbor_map_entry_vmatch (pm +. pm') entry pair ** pure (pair == pair')
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  unfold (cbor_map_entry_vmatch pm' entry pair');
  unfold (cbor_map_entry_match cbor_raw_match pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  unfold (cbor_map_entry_match cbor_raw_match pm' entry pair');
  unfold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair');
  unfold (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj entry (snd pair'));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair'))
       as (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair'));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm entry.cbor_map_entry_value (snd pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair'))
       as (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair'));
  cbor_raw_match_gather entry.cbor_map_entry_key #pm #(fst pair) #pm' #(fst pair');
  cbor_raw_match_gather entry.cbor_map_entry_value #pm #(snd pair) #pm' #(snd pair');
  rewrite (cbor_raw_match (pm +. pm') entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match (pm +. pm') (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match (pm +. pm') entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match (pm +. pm') (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match cbor_raw_match (pm +. pm') entry pair);
  fold (cbor_map_entry_vmatch (pm +. pm') entry pair);
}
```

// zero_copy_parse for map entries: read two cbor_raw values from a serialized pair
inline_for_extraction
```pulse
fn cbor_map_entry_zero_copy_parse
  (f64: squash SZ.fits_u64)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry cbor_raw
ensures cbor_map_entry_vmatch 1.0R res v **
        Trade.trade (cbor_map_entry_vmatch 1.0R res v)
                    (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  let zcp1 = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read 1.0R f64) ();
  let pair = LowParse.PulseParse.Combinators.zero_copy_parse_nondep_then jump_raw_data_item_eta zcp1 () zcp1 input;
  let entry : cbor_map_entry cbor_raw = { cbor_map_entry_key = fst pair; cbor_map_entry_value = snd pair };
  rewrite (vmatch_pair (cbor_raw_match 1.0R) (cbor_raw_match 1.0R) pair (Ghost.reveal v))
       as (cbor_map_entry_vmatch 1.0R entry v);
  rewrite (Trade.trade (vmatch_pair (cbor_raw_match 1.0R) (cbor_raw_match 1.0R) pair (Ghost.reveal v))
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v))
       as (Trade.trade (cbor_map_entry_vmatch 1.0R entry v)
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v));
  entry
}
```

```pulse
ghost
fn unfold_map_entry_vmatch
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair
ensures cbor_raw_match pm entry.cbor_map_entry_key (fst pair) **
        cbor_raw_match pm entry.cbor_map_entry_value (snd pair)
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  unfold (cbor_map_entry_match cbor_raw_match pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm entry.cbor_map_entry_value (snd pair));
}
```

```pulse
ghost
fn fold_map_entry_vmatch
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
requires cbor_raw_match pm entry.cbor_map_entry_key (fst pair) **
         cbor_raw_match pm entry.cbor_map_entry_value (snd pair)
ensures cbor_map_entry_vmatch pm entry pair
{
  rewrite (cbor_raw_match pm entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match pm entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match cbor_raw_match pm entry pair);
  fold (cbor_map_entry_vmatch pm entry pair);
}
```
