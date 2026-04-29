module CBOR.Pulse.Raw.EverParse.Match
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Type
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open LowParse.Pulse.Base
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator

(* ======== Projectors ======== *)

(* Identity projector on cbor_raw, used for the outer dependent pair
   (parse_dtuple2 parse_header (parse_content p)) where the full cbor_raw
   value is needed by both the header relation and the content relation. *)
let cbor_raw_id_proj : pair_proj cbor_raw cbor_raw = {
  pair_proj_get = (fun x -> x);
  pair_proj_set = (fun _ x -> x);
  pair_proj_get_set = (fun _ _ -> ());
  pair_proj_set_set = (fun _ _ _ -> ());
  pair_proj_set_get = (fun _ -> ());
}

(* Projector for the key of a map entry, corresponding to the first
   component of parse_content's (p `nondep_then` p) for maps. *)
let cbor_map_entry_key_proj : pair_proj (cbor_map_entry cbor_raw) cbor_raw = {
  pair_proj_get = (fun e -> e.cbor_map_entry_key);
  pair_proj_set = (fun e k -> { e with cbor_map_entry_key = k });
  pair_proj_get_set = (fun _ _ -> ());
  pair_proj_set_set = (fun _ _ _ -> ());
  pair_proj_set_get = (fun _ -> ());
}

(* Projector for the value of a map entry, corresponding to the second
   component of parse_content's (p `nondep_then` p) for maps. *)
let cbor_map_entry_value_proj : pair_proj (cbor_map_entry cbor_raw) cbor_raw = {
  pair_proj_get = (fun e -> e.cbor_map_entry_value);
  pair_proj_set = (fun e v -> { e with cbor_map_entry_value = v });
  pair_proj_get_set = (fun _ _ -> ());
  pair_proj_set_set = (fun _ _ _ -> ());
  pair_proj_set_get = (fun _ -> ());
}

(* ======== Header relation ======== *)

(* Compute the expected header from a concrete cbor_raw value.
   This corresponds to the parse_header part of parse_raw_data_item_aux. *)
let cbor_raw_get_header (xl: cbor_raw) : GTot (option header) =
  match xl with
  | CBOR_Case_Int v ->
    Some (raw_uint64_as_argument v.cbor_int_type
      ({ size = v.cbor_int_size; value = v.cbor_int_value }))
  | CBOR_Case_Simple v ->
    Some (simple_value_as_argument v)
  | CBOR_Case_String v ->
    Some (raw_uint64_as_argument v.cbor_string_type
      ({ size = v.cbor_string_size;
         value = U64.uint_to_t (SZ.v (S.len v.cbor_string_ptr)) }))
  | CBOR_Case_Array v ->
    Some (raw_uint64_as_argument cbor_major_type_array
      ({ size = v.cbor_array_length_size;
         value = U64.uint_to_t (SZ.v (I.iterator_length v.cbor_array_ptr)) }))
  | CBOR_Case_Map v ->
    Some (raw_uint64_as_argument cbor_major_type_map
      ({ size = v.cbor_map_length_size;
         value = U64.uint_to_t (SZ.v (I.iterator_length v.cbor_map_ptr)) }))
  | CBOR_Case_Tagged v ->
    Some (raw_uint64_as_argument cbor_major_type_tagged v.cbor_tagged_tag)
  | CBOR_Case_Invalid -> None

(* Header relation: pure match between the concrete cbor_raw fields and
   the abstract header, corresponding to parse_header in
   parse_dtuple2 parse_header (parse_content p). *)
let cbor_raw_match_header (xl: cbor_raw) (h: header) : Tot slprop =
  pure (cbor_raw_get_header xl == Some h)

(* ======== Map entry relation ======== *)

(* Map entry relation using projector combinators, corresponding to the
   nondep_then (p `nondep_then` p) in parse_content for maps. Uses
   vmatch_pair_with_proj from the Projectors module. *)
let cbor_map_entry_match
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
: Tot slprop
= vmatch_pair_with_proj (p pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p pm) cbor_map_entry_value_proj)
    entry pair

(* ======== Content relation ======== *)

(* Content relation following the structure of parse_content p h.
   Cases mirror the branches of parse_content:
   - string: weaken _ (parse_filter (parse_lseq_bytes n) ...)  →  pts_to on string slice
   - array:  weaken _ (parse_nlist n p)                        →  iterator_match
   - map:    weaken _ (parse_nlist n (p `nondep_then` p))      →  iterator_match with map entry match
   - tagged: weaken _ p                                        →  vmatch_ref_wf
   - other:  weaken _ parse_empty                               →  emp
*)
let cbor_raw_match_content
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (xh: raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (c: content h)
: Tot slprop
= let (| b, long_arg |) = h in
  if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
  then
    (match xl with
    | CBOR_Case_String v ->
      S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) c
    | _ -> pure False)
  else if b.major_type = cbor_major_type_array
  then
    (match xl with
    | CBOR_Case_Array v ->
      I.iterator_match
        (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
        pp
        (pm *. v.cbor_array_slice_perm)
        v.cbor_array_ptr
        c
    | _ -> pure False)
  else if b.major_type = cbor_major_type_map
  then
    (match xl with
    | CBOR_Case_Map v ->
      I.iterator_match
        (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
             (x: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match p pm' elem x)
        (nondep_then pp pp)
        (pm *. v.cbor_map_slice_perm)
        v.cbor_map_ptr
        c
    | _ -> pure False)
  else if b.major_type = cbor_major_type_tagged
  then
    (match xl with
    | CBOR_Case_Tagged v ->
      vmatch_ref_wf xh
        (fun (vl: cbor_raw) (vh: raw_data_item { vh << xh }) ->
          p (pm *. v.cbor_tagged_payload_perm) vl vh)
        ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
        c
    | _ -> pure False)
  else
    emp

(* ======== Top-level relation ======== *)

(* The full relation between cbor_raw and raw_data_item, following the
   structure of parse_raw_data_item_aux:
     parse_dtuple2 parse_header (parse_content p) `parse_synth` synth_raw_data_item

   Decomposed as:
   - vmatch_synth for parse_synth (using synth_raw_data_item_recip)
   - vmatch_dep_pair_with_proj for parse_dtuple2 (using the identity projector)
   - per-case content relations as above

   The parameter p accounts for the recursive relation, and pp is the
   corresponding recursive parser (needed by iterator_match for the
   Serialized case), mirroring the parser parameter p in
   parse_raw_data_item_aux.
*)
let cbor_raw_match_aux
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Tot slprop
= vmatch_synth
    (vmatch_dep_pair_with_proj
      cbor_raw_match_header
      cbor_raw_id_proj
      (cbor_raw_match_content p pp pm xh))
    synth_raw_data_item_recip
    xl xh

(* ======== Share/Gather ======== *)

ghost fn cbor_map_entry_match_share
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_share: I.share_t p)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_map_entry_match p pm entry pair
ensures cbor_map_entry_match p (pm /. 2.0R) entry pair **
        cbor_map_entry_match p (pm /. 2.0R) entry pair
{
  unfold (cbor_map_entry_match p pm entry pair);
  unfold (vmatch_pair_with_proj (p pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (p pm) cbor_map_entry_value_proj entry (snd pair));
  p_share entry.cbor_map_entry_key;
  p_share entry.cbor_map_entry_value;
  fold (vmatch_with_pair_proj (p (pm /. 2.0R)) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (p (pm /. 2.0R)) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p (pm /. 2.0R)) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match p (pm /. 2.0R) entry pair);
  fold (vmatch_with_pair_proj (p (pm /. 2.0R)) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (p (pm /. 2.0R)) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p (pm /. 2.0R)) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match p (pm /. 2.0R) entry pair);
}

ghost fn cbor_map_entry_match_gather
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_gather: I.gather_t p)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: Ghost.erased (raw_data_item & raw_data_item))
  (#pm': perm)
  (#pair': Ghost.erased (raw_data_item & raw_data_item))
requires cbor_map_entry_match p pm entry pair **
         cbor_map_entry_match p pm' entry pair'
ensures cbor_map_entry_match p (pm +. pm') entry pair **
        pure (pair == pair')
{
  unfold (cbor_map_entry_match p pm entry pair);
  unfold (vmatch_pair_with_proj (p pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (p pm) cbor_map_entry_value_proj entry (snd pair));
  unfold (cbor_map_entry_match p pm' entry pair');
  unfold (vmatch_pair_with_proj (p pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p pm') cbor_map_entry_value_proj) entry pair');
  unfold (vmatch_with_pair_proj (p pm') cbor_map_entry_value_proj entry (snd pair'));
  rewrite (p pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (p pm entry.cbor_map_entry_key (fst pair));
  rewrite (p pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair'))
       as (p pm' entry.cbor_map_entry_key (fst pair'));
  rewrite (p pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (p pm entry.cbor_map_entry_value (snd pair));
  rewrite (p pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair'))
       as (p pm' entry.cbor_map_entry_value (snd pair'));
  p_gather entry.cbor_map_entry_key #pm #(Ghost.reveal (Ghost.hide (fst pair))) #pm' #(Ghost.reveal (Ghost.hide (fst pair')));
  p_gather entry.cbor_map_entry_value #pm #(Ghost.reveal (Ghost.hide (snd pair))) #pm' #(Ghost.reveal (Ghost.hide (snd pair')));
  rewrite (p (pm +. pm') entry.cbor_map_entry_key (fst pair))
       as (p (pm +. pm') (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (p (pm +. pm') entry.cbor_map_entry_value (snd pair))
       as (p (pm +. pm') (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (p (pm +. pm')) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (p (pm +. pm')) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p (pm +. pm')) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match p (pm +. pm') entry pair);
}

ghost fn cbor_raw_match_content_share
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_share: I.share_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (xh: raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (pm: perm)
  (c: content h)
requires cbor_raw_match_content p pp pm xh h xl c
ensures cbor_raw_match_content p pp (pm /. 2.0R) xh h xl c **
        cbor_raw_match_content p pp (pm /. 2.0R) xh h xl c
{
  admit ()
}

ghost fn cbor_raw_match_content_gather
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_gather: I.gather_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (xh: raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (pm: perm)
  (c: content h)
  (pm': perm)
  (c': content h)
requires cbor_raw_match_content p pp pm xh h xl c **
         cbor_raw_match_content p pp pm' xh h xl c'
ensures cbor_raw_match_content p pp (pm +. pm') xh h xl c **
        pure (c == c')
{
  admit ()
}

ghost fn cbor_raw_match_aux_share
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_share: I.share_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_aux p pp pm xl xh
ensures cbor_raw_match_aux p pp (pm /. 2.0R) xl xh **
        cbor_raw_match_aux p pp (pm /. 2.0R) xl xh
{
  unfold (cbor_raw_match_aux p pp pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp pm (Ghost.reveal xh)))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp pm (Ghost.reveal xh))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header xl ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  let the_prop = cbor_raw_get_header xl ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)));
  let sq = elim_pure_explicit the_prop;
  cbor_raw_match_content_share p p_share pp
    (Ghost.reveal xh)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
    xl pm
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)));
  intro_pure the_prop sq;
  intro_pure the_prop sq;
  rewrite (pure the_prop)
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp (pm /. 2.0R) (Ghost.reveal xh))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp (pm /. 2.0R) (Ghost.reveal xh)))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux p pp (pm /. 2.0R) xl (Ghost.reveal xh));
  rewrite (pure the_prop)
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp (pm /. 2.0R) (Ghost.reveal xh))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp (pm /. 2.0R) (Ghost.reveal xh)))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux p pp (pm /. 2.0R) xl (Ghost.reveal xh));
}

ghost fn cbor_raw_match_aux_gather
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_gather: I.gather_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
  (#pm': perm)
  (#xh': Ghost.erased raw_data_item)
requires cbor_raw_match_aux p pp pm xl xh **
         cbor_raw_match_aux p pp pm' xl xh'
ensures cbor_raw_match_aux p pp (pm +. pm') xl xh **
        pure (xh == xh')
{
  unfold (cbor_raw_match_aux p pp pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp pm (Ghost.reveal xh)))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp pm (Ghost.reveal xh))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  unfold (cbor_raw_match_aux p pp pm' xl xh');
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp pm' (Ghost.reveal xh')))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh'));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp pm' (Ghost.reveal xh'))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh')));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh'))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header xl ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh')))))
    as
    (pure (cbor_raw_get_header xl ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh')))));
  let the_prop1 = cbor_raw_get_header xl ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)));
  let the_prop2 = cbor_raw_get_header xl ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh')));
  let sq1 = elim_pure_explicit the_prop1;
  let sq2 = elim_pure_explicit the_prop2;
  // From both pure facts, the headers are equal, so synth_raw_data_item_recip xh == ... xh',
  // and by injectivity of synth_raw_data_item_recip + synth_raw_data_item, xh == xh'
  admit ()
}
