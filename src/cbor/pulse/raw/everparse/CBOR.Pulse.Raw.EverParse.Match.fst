module CBOR.Pulse.Raw.EverParse.Match
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Type
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open LowParse.Pulse.Base
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Base
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
         value = U64.uint_to_t (SZ.v (I.mixed_list_length v.cbor_array_ptr)) }))
  | CBOR_Case_Map v ->
    Some (raw_uint64_as_argument cbor_major_type_map
      ({ size = v.cbor_map_length_size;
         value = U64.uint_to_t (SZ.v (I.mixed_list_length v.cbor_map_ptr)) }))
  | CBOR_Case_Tagged v ->
    Some (raw_uint64_as_argument cbor_major_type_tagged v.cbor_tagged_tag)
  | CBOR_Case_Tagged_Serialized v ->
    Some (raw_uint64_as_argument cbor_major_type_tagged v.cbor_tagged_serialized_tag)
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

(* Content coercion helper for tagged case — needed in definition *)
let content_as_raw_data_item
  (b: initial_byte)
  (la: long_argument b)
  (c: content (| b, la |))
  : Tot raw_data_item
= if b.major_type = cbor_major_type_tagged
  then c
  else Simple 0uy

(* Helper slprop for the tagged case, avoiding inline lambdas in rewrite targets *)
[@@"opaque_to_smt"]
let cbor_tagged_content_slprop
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm)
  (v: cbor_tagged cbor_raw)
  (cr: raw_data_item)
: Tot slprop
= vmatch_ref
    (fun (vl: cbor_raw) (vh: raw_data_item) ->
      p (pm *. v.cbor_tagged_payload_perm) vl vh)
    ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
    cr

(* Content relation following the structure of parse_content p h.
   Cases mirror the branches of parse_content:
   - string: weaken _ (parse_filter (parse_lseq_bytes n) ...)  →  pts_to on string slice
   - array:  weaken _ (parse_nlist n p)                        →  mixed_list_match
   - map:    weaken _ (parse_nlist n (p `nondep_then` p))      →  mixed_list_match with map entry match
   - tagged: weaken _ p                                        →  vmatch_ref_wf
   - other:  weaken _ parse_empty                               →  emp
*)
let cbor_raw_match_content
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (h: header)
  (xl: cbor_raw)
  (c: content h)
: Tot slprop
= let (| b, long_arg |) = h in
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
  then
    (match xl with
    | CBOR_Case_String v ->
      S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) c
    | _ -> pure False)
  else if (b.major_type = cbor_major_type_array)
  then
    (match xl with
    | CBOR_Case_Array v ->
      I.mixed_list_match
        (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
        pp
        (pm *. v.cbor_array_slice_perm)
        v.cbor_array_ptr
        c
    | _ -> pure False)
  else if (b.major_type = cbor_major_type_map)
  then
    (match xl with
    | CBOR_Case_Map v ->
      I.mixed_list_match
        (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
             (x: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match p pm' elem x)
        (nondep_then pp pp)
        (pm *. v.cbor_map_slice_perm)
        v.cbor_map_ptr
        c
    | _ -> pure False)
  else if (b.major_type = cbor_major_type_tagged)
  then
    (match xl with
    | CBOR_Case_Tagged v ->
      cbor_tagged_content_slprop p pm v (content_as_raw_data_item b long_arg c)
    | CBOR_Case_Tagged_Serialized v ->
      pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b long_arg c)
    | _ -> pure False)
  else
    emp

(* ======== Helper lemmas ======== *)

let header_eta (h: header)
  : Lemma (h == (| dfst h, dsnd h |))
= match h with | Mkdtuple2 _ _ -> ()

let content_eq_other
  (b: initial_byte)
  (la: long_argument b)
  (c c': content (| b, la |))
  : Lemma
    (requires
      b.major_type <> cbor_major_type_byte_string /\
      b.major_type <> cbor_major_type_text_string /\
      b.major_type <> cbor_major_type_array /\
      b.major_type <> cbor_major_type_map /\
      b.major_type <> cbor_major_type_tagged)
    (ensures c == c')
= assert_norm (content (| b, la |) ==
    (if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
     then parse_filter_refine (lseq_utf8_correct b.major_type (U64.v (argument_as_uint64 b la)))
     else if (b.major_type = cbor_major_type_array)
     then nlist (U64.v (argument_as_uint64 b la)) raw_data_item
     else if (b.major_type = cbor_major_type_map)
     then nlist (U64.v (argument_as_uint64 b la)) (raw_data_item & raw_data_item)
     else if (b.major_type = cbor_major_type_tagged)
     then raw_data_item
     else unit))

let vmatch_ref_wf_false
  (#tbound: Type)
  (#tl #th: Type0)
  (bound: tbound)
  (vmatch: tl -> (vh: th { vh << bound }) -> slprop)
  (r: with_perm (ref tl))
  (vh: th)
  : Lemma
    (requires ~ (vh << bound))
    (ensures vmatch_ref_wf bound vmatch r vh == pure False)
= let b = FStar.StrongExcludedMiddle.strong_excluded_middle (vh << bound) in
  assert_norm (vmatch_ref_wf bound vmatch r vh ==
    (if FStar.StrongExcludedMiddle.strong_excluded_middle (vh << bound)
     then vmatch_ref_wf0 bound vmatch r vh (Some ())
     else pure False));
  assert (b == false)

(* ======== Content coercion helpers ======== *)

(* These functions coerce content (| b, la |) to the concrete type expected
   by the relation combinators (S.pts_to, mixed_list_match, vmatch_ref_wf).
   This is needed because Pulse's elaborator cannot reduce `content (| b, la |)`
   when b is symbolic, even inside an if-branch where b.major_type is known.
   They are defined as total functions (no precondition) using conditionals
   so they can appear in Pulse rewrite target expressions. *)

let content_as_seq_u8
  (b: initial_byte)
  (la: long_argument b)
  (c: content (| b, la |))
  : Tot (Seq.seq U8.t)
= if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
  then c
  else Seq.empty

let content_as_list_raw
  (b: initial_byte)
  (la: long_argument b)
  (c: content (| b, la |))
  : Tot (list raw_data_item)
= if b.major_type = cbor_major_type_array
  then c
  else []

let content_as_list_pair
  (b: initial_byte)
  (la: long_argument b)
  (c: content (| b, la |))
  : Tot (list (raw_data_item & raw_data_item))
= if b.major_type = cbor_major_type_map
  then c
  else []

(* ======== Unfolding lemmas ======== *)

(* These lemmas establish what cbor_raw_match_content equals in each case.
   Used in Pulse share/gather proofs via lemma call + rewrite, avoiding
   the issue where Pulse's unfold doesn't reduce the if-chain.
   The RHS uses content coercion helpers so Pulse can elaborate the rewrite target. *)

#push-options "--z3rlimit 32"

let cbor_raw_match_content_eq_string
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (b: initial_byte)
  (la: long_argument b)
  (v: cbor_string)
  (c: content (| b, la |))
  : Lemma
    (requires (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) == true)
    (ensures cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String v) c ==
             S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c))
= ()

let cbor_raw_match_content_eq_array
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (b: initial_byte)
  (la: long_argument b)
  (v: cbor_array cbor_raw)
  (c: content (| b, la |))
  : Lemma
    (requires b.major_type = cbor_major_type_array)
    (ensures cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array v) c ==
             I.mixed_list_match
               (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
               pp
               (pm *. v.cbor_array_slice_perm)
               v.cbor_array_ptr
               (content_as_list_raw b la c))
= ()

let cbor_raw_match_content_eq_map
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (b: initial_byte)
  (la: long_argument b)
  (v: cbor_map cbor_raw)
  (c: content (| b, la |))
  : Lemma
    (requires b.major_type = cbor_major_type_map)
    (ensures cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map v) c ==
             I.mixed_list_match
               (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                    (x: (raw_data_item & raw_data_item)) ->
                 cbor_map_entry_match p pm' elem x)
               (nondep_then pp pp)
               (pm *. v.cbor_map_slice_perm)
               v.cbor_map_ptr
               (content_as_list_pair b la c))
= ()

let cbor_raw_match_content_eq_tagged
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (b: initial_byte)
  (la: long_argument b)
  (v: cbor_tagged cbor_raw)
  (c: content (| b, la |))
  : Lemma
    (requires b.major_type = cbor_major_type_tagged)
    (ensures cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged v) c ==
             cbor_tagged_content_slprop p pm v (content_as_raw_data_item b la c))
= ()

let cbor_raw_match_content_eq_tagged_serialized
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (b: initial_byte)
  (la: long_argument b)
  (v: cbor_tagged_serialized)
  (c: content (| b, la |))
  : Lemma
    (requires b.major_type = cbor_major_type_tagged)
    (ensures cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c ==
             pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
= ()

let cbor_raw_match_content_eq_other
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm: perm)
  (b: initial_byte)
  (la: long_argument b)
  (xl: cbor_raw)
  (c: content (| b, la |))
  : Lemma
    (requires
      b.major_type <> cbor_major_type_byte_string /\
      b.major_type <> cbor_major_type_text_string /\
      b.major_type <> cbor_major_type_array /\
      b.major_type <> cbor_major_type_map /\
      b.major_type <> cbor_major_type_tagged)
    (ensures cbor_raw_match_content p pp pm (| b, la |) xl c == emp)
= ()

#pop-options

(* ======== Top-level relation ======== *)

(* The full relation between cbor_raw and raw_data_item, following the
   structure of parse_raw_data_item_aux:
     parse_dtuple2 parse_header (parse_content p) `parse_synth` synth_raw_data_item

   Decomposed as:
   - vmatch_synth for parse_synth (using synth_raw_data_item_recip)
   - vmatch_dep_pair_with_proj for parse_dtuple2 (using the identity projector)
   - per-case content relations as above

   The parameter p accounts for the recursive relation, and pp is the
   corresponding recursive parser (needed by mixed_list_match for the
   Serialized case), mirroring the parser parameter p in
   parse_raw_data_item_aux.
*)
let cbor_raw_match_aux
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Tot slprop
= vmatch_synth
    (vmatch_dep_pair_with_proj
      cbor_raw_match_header
      cbor_raw_id_proj
      (cbor_raw_match_content p pp pm))
    synth_raw_data_item_recip
    xl xh

(* ======== Share/Gather ======== *)

ghost fn cbor_map_entry_match_share
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_share: I.share_t p)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: (raw_data_item & raw_data_item))
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
  (#pair: (raw_data_item & raw_data_item))
  (#pm': perm)
  (#pair': (raw_data_item & raw_data_item))
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

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

ghost fn cbor_raw_match_content_share
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_share: I.share_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (pm: perm)
  (c: content h)
requires cbor_raw_match_content p pp pm h xl c
ensures cbor_raw_match_content p pp (pm /. 2.0R) h xl c **
        cbor_raw_match_content p pp (pm /. 2.0R) h xl c
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite (cbor_raw_match_content p pp pm h xl c)
       as (cbor_raw_match_content p pp pm (| b, la |) xl c);
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) {
    match xl {
      CBOR_Case_String v -> {
        cbor_raw_match_content_eq_string p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String v) c)
             as (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        S.share v.cbor_string_ptr;
        rewrite (S.pts_to v.cbor_string_ptr #((pm *. v.cbor_string_perm) /. 2.0R) (content_as_seq_u8 b la c))
             as (S.pts_to v.cbor_string_ptr #((pm /. 2.0R) *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        rewrite (S.pts_to v.cbor_string_ptr #((pm *. v.cbor_string_perm) /. 2.0R) (content_as_seq_u8 b la c))
             as (S.pts_to v.cbor_string_ptr #((pm /. 2.0R) *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        cbor_raw_match_content_eq_string p pp (pm /. 2.0R) b la v c;
        rewrite (S.pts_to v.cbor_string_ptr #((pm /. 2.0R) *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_String v) c);
        rewrite (S.pts_to v.cbor_string_ptr #((pm /. 2.0R) *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_String v) c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_String v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_String v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_array) {
    match xl {
      CBOR_Case_Array v -> {
        cbor_raw_match_content_eq_array p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        I.mixed_list_match_share
          (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
          (fun (x1: cbor_raw) (#pm': perm) (#x2: raw_data_item) -> p_share x1 #pm' #x2)
          pp
          v.cbor_array_ptr;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   ((pm *. v.cbor_array_slice_perm) /. 2.0R)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   ((pm /. 2.0R) *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   ((pm *. v.cbor_array_slice_perm) /. 2.0R)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   ((pm /. 2.0R) *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        cbor_raw_match_content_eq_array p pp (pm /. 2.0R) b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   ((pm /. 2.0R) *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Array v) c);
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
                   pp
                   ((pm /. 2.0R) *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Array v) c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Array v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Array v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_map) {
    match xl {
      CBOR_Case_Map v -> {
        cbor_raw_match_content_eq_map p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map v) c)
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        I.mixed_list_match_share
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
               (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match p pm' elem x)
          (fun (x1: cbor_map_entry cbor_raw) (#pm': perm) (#x2: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match_share p p_share x1 #pm' #x2)
          (nondep_then pp pp)
          v.cbor_map_ptr;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   ((pm *. v.cbor_map_slice_perm) /. 2.0R)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   ((pm /. 2.0R) *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   ((pm *. v.cbor_map_slice_perm) /. 2.0R)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   ((pm /. 2.0R) *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        cbor_raw_match_content_eq_map p pp (pm /. 2.0R) b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   ((pm /. 2.0R) *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Map v) c);
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   ((pm /. 2.0R) *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Map v) c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Map v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Map v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_tagged) {
    match xl {
      CBOR_Case_Tagged v -> {
        cbor_raw_match_content_eq_tagged p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_tagged_content_slprop p pm v (content_as_raw_data_item b la c));
        unfold (cbor_tagged_content_slprop p pm v (content_as_raw_data_item b la c));
        unfold (vmatch_ref
          (fun (vl: cbor_raw) (vh: raw_data_item) -> p (pm *. v.cbor_tagged_payload_perm) vl vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
          p (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        R.share v.cbor_tagged_ptr;
        rewrite (R.pts_to v.cbor_tagged_ptr #((pm *. v.cbor_tagged_ref_perm) /. 2.0R) vl)
             as (R.pts_to v.cbor_tagged_ptr #((pm /. 2.0R) *. v.cbor_tagged_ref_perm) vl);
        rewrite (R.pts_to v.cbor_tagged_ptr #((pm *. v.cbor_tagged_ref_perm) /. 2.0R) vl)
             as (R.pts_to v.cbor_tagged_ptr #((pm /. 2.0R) *. v.cbor_tagged_ref_perm) vl);
        p_share vl;
        rewrite (p ((pm *. v.cbor_tagged_payload_perm) /. 2.0R) vl (content_as_raw_data_item b la c))
             as (p ((pm /. 2.0R) *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        rewrite (p ((pm *. v.cbor_tagged_payload_perm) /. 2.0R) vl (content_as_raw_data_item b la c))
             as (p ((pm /. 2.0R) *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        fold (vmatch_ref
          (fun (vl': cbor_raw) (vh: raw_data_item) -> p ((pm /. 2.0R) *. v.cbor_tagged_payload_perm) vl' vh)
          ({ v = v.cbor_tagged_ptr; p = (pm /. 2.0R) *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        fold (cbor_tagged_content_slprop p (pm /. 2.0R) v (content_as_raw_data_item b la c));
        fold (vmatch_ref
          (fun (vl': cbor_raw) (vh: raw_data_item) -> p ((pm /. 2.0R) *. v.cbor_tagged_payload_perm) vl' vh)
          ({ v = v.cbor_tagged_ptr; p = (pm /. 2.0R) *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        fold (cbor_tagged_content_slprop p (pm /. 2.0R) v (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged p pp (pm /. 2.0R) b la v c;
        rewrite (cbor_tagged_content_slprop p (pm /. 2.0R) v (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged v) c);
        rewrite (cbor_tagged_content_slprop p (pm /. 2.0R) v (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged v) c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
      }
      CBOR_Case_Tagged_Serialized v -> {
        cbor_raw_match_content_eq_tagged_serialized p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        I.pts_to_parsed_strong_prefix_share pp v.cbor_tagged_serialized_ptr;
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm *. v.cbor_tagged_serialized_slice_perm) /. 2.0R) (content_as_raw_data_item b la c))
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm /. 2.0R) *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm *. v.cbor_tagged_serialized_slice_perm) /. 2.0R) (content_as_raw_data_item b la c))
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm /. 2.0R) *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged_serialized p pp (pm /. 2.0R) b la v c;
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm /. 2.0R) *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged_Serialized v) c);
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm /. 2.0R) *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged_Serialized v) c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
        rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else {
    cbor_raw_match_content_eq_other p pp pm b la xl c;
    rewrite (cbor_raw_match_content p pp pm (| b, la |) xl c) as emp;
    dup_emp ();
    cbor_raw_match_content_eq_other p pp (pm /. 2.0R) b la xl c;
    rewrite emp as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) xl c);
    rewrite emp as (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) xl c);
    rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) xl c)
         as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
    rewrite (cbor_raw_match_content p pp (pm /. 2.0R) (| b, la |) xl c)
         as (cbor_raw_match_content p pp (pm /. 2.0R) h xl c);
  }
}

ghost fn cbor_raw_match_content_gather
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_gather: I.gather_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (pm: perm)
  (c: content h)
  (pm': perm)
  (c': content h)
requires cbor_raw_match_content p pp pm h xl c **
         cbor_raw_match_content p pp pm' h xl c'
ensures cbor_raw_match_content p pp (pm +. pm') h xl c **
        pure (c == c')
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite (cbor_raw_match_content p pp pm h xl c)
       as (cbor_raw_match_content p pp pm (| b, la |) xl c);
  rewrite (cbor_raw_match_content p pp pm' h xl c')
       as (cbor_raw_match_content p pp pm' (| b, la |) xl c');
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) {
    match xl {
      CBOR_Case_String v -> {
        cbor_raw_match_content_eq_string p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String v) c)
             as (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        cbor_raw_match_content_eq_string p pp pm' b la v c';
        rewrite (cbor_raw_match_content p pp pm' (| b, la |) (CBOR_Case_String v) c')
             as (S.pts_to v.cbor_string_ptr #(pm' *. v.cbor_string_perm) (content_as_seq_u8 b la c'));
        S.gather v.cbor_string_ptr;
        rewrite (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm +. pm' *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (S.pts_to v.cbor_string_ptr #((pm +. pm') *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        cbor_raw_match_content_eq_string p pp (pm +. pm') b la v c;
        rewrite (S.pts_to v.cbor_string_ptr #((pm +. pm') *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_String v) c);
        rewrite (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_String v) c)
             as (cbor_raw_match_content p pp (pm +. pm') h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_array) {
    match xl {
      CBOR_Case_Array v -> {
        cbor_raw_match_content_eq_array p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp (pm *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c));
        cbor_raw_match_content_eq_array p pp pm' b la v c';
        rewrite (cbor_raw_match_content p pp pm' (| b, la |) (CBOR_Case_Array v) c')
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp (pm' *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c'));
        let cl = content_as_list_raw b la c;
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp (pm *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c))
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp (pm *. v.cbor_array_slice_perm) v.cbor_array_ptr cl);
        let c'l = content_as_list_raw b la c';
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp (pm' *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c'))
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp (pm' *. v.cbor_array_slice_perm) v.cbor_array_ptr c'l);
        I.mixed_list_match_gather
          (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
          (fun (x1: cbor_raw) (#pm'': perm) (#x2: raw_data_item) (#pm3: perm) (#x3: raw_data_item) ->
            p_gather x1 #pm'' #x2 #pm3 #x3)
          pp
          v.cbor_array_ptr
          (pm *. v.cbor_array_slice_perm)
          #cl
          (pm' *. v.cbor_array_slice_perm)
          #c'l;
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp
                   (pm *. v.cbor_array_slice_perm +. pm' *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   cl)
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp
                   ((pm +. pm') *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        cbor_raw_match_content_eq_array p pp (pm +. pm') b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm'' elem x)
                   pp ((pm +. pm') *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c))
             as (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Array v) c);
        rewrite (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Array v) c)
             as (cbor_raw_match_content p pp (pm +. pm') h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_map) {
    match xl {
      CBOR_Case_Map v -> {
        cbor_raw_match_content_eq_map p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map v) c)
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) (pm *. v.cbor_map_slice_perm) v.cbor_map_ptr (content_as_list_pair b la c));
        cbor_raw_match_content_eq_map p pp pm' b la v c';
        rewrite (cbor_raw_match_content p pp pm' (| b, la |) (CBOR_Case_Map v) c')
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) (pm' *. v.cbor_map_slice_perm) v.cbor_map_ptr (content_as_list_pair b la c'));
        let cl = content_as_list_pair b la c;
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) (pm *. v.cbor_map_slice_perm) v.cbor_map_ptr (content_as_list_pair b la c))
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) (pm *. v.cbor_map_slice_perm) v.cbor_map_ptr cl);
        let c'l = content_as_list_pair b la c';
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) (pm' *. v.cbor_map_slice_perm) v.cbor_map_ptr (content_as_list_pair b la c'))
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) (pm' *. v.cbor_map_slice_perm) v.cbor_map_ptr c'l);
        I.mixed_list_match_gather
          (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
               (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match p pm'' elem x)
          (fun (x1: cbor_map_entry cbor_raw) (#pm'': perm) (#x2: (raw_data_item & raw_data_item))
               (#pm3: perm) (#x3: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match_gather p p_gather x1 #pm'' #x2 #pm3 #x3)
          (nondep_then pp pp)
          v.cbor_map_ptr
          (pm *. v.cbor_map_slice_perm)
          #cl
          (pm' *. v.cbor_map_slice_perm)
          #c'l;
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm +. pm' *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   cl)
             as (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp)
                   ((pm +. pm') *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        cbor_raw_match_content_eq_map p pp (pm +. pm') b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm'': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm'' elem x)
                   (nondep_then pp pp) ((pm +. pm') *. v.cbor_map_slice_perm) v.cbor_map_ptr (content_as_list_pair b la c))
             as (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Map v) c);
        rewrite (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Map v) c)
             as (cbor_raw_match_content p pp (pm +. pm') h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_tagged) {
    match xl {
      CBOR_Case_Tagged v -> {
        cbor_raw_match_content_eq_tagged p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_tagged_content_slprop p pm v (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged p pp pm' b la v c';
        rewrite (cbor_raw_match_content p pp pm' (| b, la |) (CBOR_Case_Tagged v) c')
             as (cbor_tagged_content_slprop p pm' v (content_as_raw_data_item b la c'));
        unfold (cbor_tagged_content_slprop p pm v (content_as_raw_data_item b la c));
        unfold (vmatch_ref
          (fun (vl: cbor_raw) (vh: raw_data_item) -> p (pm *. v.cbor_tagged_payload_perm) vl vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        unfold (cbor_tagged_content_slprop p pm' v (content_as_raw_data_item b la c'));
        unfold (vmatch_ref
          (fun (vl: cbor_raw) (vh: raw_data_item) -> p (pm' *. v.cbor_tagged_payload_perm) vl vh)
          ({ v = v.cbor_tagged_ptr; p = pm' *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c'));
        with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
          p (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        with vl' . assert (R.pts_to v.cbor_tagged_ptr #(pm' *. v.cbor_tagged_ref_perm) vl' **
          p (pm' *. v.cbor_tagged_payload_perm) vl' (content_as_raw_data_item b la c'));
        R.gather v.cbor_tagged_ptr;
        rewrite (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm +. pm' *. v.cbor_tagged_ref_perm) vl)
             as (R.pts_to v.cbor_tagged_ptr #((pm +. pm') *. v.cbor_tagged_ref_perm) vl);
        // R.gather gives us vl == vl'
        rewrite (p (pm' *. v.cbor_tagged_payload_perm) vl' (content_as_raw_data_item b la c'))
             as (p (pm' *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c'));
        p_gather vl
          #(pm *. v.cbor_tagged_payload_perm) #(content_as_raw_data_item b la c)
          #(pm' *. v.cbor_tagged_payload_perm) #(content_as_raw_data_item b la c');
        // p_gather gives us content_as_raw_data_item b la c == content_as_raw_data_item b la c'
        rewrite (p (pm *. v.cbor_tagged_payload_perm +. pm' *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c))
             as (p ((pm +. pm') *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        fold (vmatch_ref
          (fun (vl': cbor_raw) (vh: raw_data_item) -> p ((pm +. pm') *. v.cbor_tagged_payload_perm) vl' vh)
          ({ v = v.cbor_tagged_ptr; p = (pm +. pm') *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        fold (cbor_tagged_content_slprop p (pm +. pm') v (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged p pp (pm +. pm') b la v c;
        rewrite (cbor_tagged_content_slprop p (pm +. pm') v (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Tagged v) c);
        rewrite (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_raw_match_content p pp (pm +. pm') h xl c);
      }
      CBOR_Case_Tagged_Serialized v -> {
        cbor_raw_match_content_eq_tagged_serialized p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged_serialized p pp pm' b la v c';
        rewrite (cbor_raw_match_content p pp pm' (| b, la |) (CBOR_Case_Tagged_Serialized v) c')
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm' *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c'));
        I.pts_to_parsed_strong_prefix_gather pp v.cbor_tagged_serialized_ptr
          #(pm *. v.cbor_tagged_serialized_slice_perm) #(content_as_raw_data_item b la c)
          #(pm' *. v.cbor_tagged_serialized_slice_perm) #(content_as_raw_data_item b la c');
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm +. pm' *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm +. pm') *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged_serialized p pp (pm +. pm') b la v c;
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #((pm +. pm') *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Tagged_Serialized v) c);
        rewrite (cbor_raw_match_content p pp (pm +. pm') (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (cbor_raw_match_content p pp (pm +. pm') h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else {
    cbor_raw_match_content_eq_other p pp pm b la xl c;
    rewrite (cbor_raw_match_content p pp pm (| b, la |) xl c) as emp;
    cbor_raw_match_content_eq_other p pp pm' b la xl c';
    rewrite (cbor_raw_match_content p pp pm' (| b, la |) xl c') as emp;
    content_eq_other b la c c';
    cbor_raw_match_content_eq_other p pp (pm +. pm') b la xl c;
    rewrite emp as (cbor_raw_match_content p pp (pm +. pm') (| b, la |) xl c);
    rewrite (cbor_raw_match_content p pp (pm +. pm') (| b, la |) xl c)
         as (cbor_raw_match_content p pp (pm +. pm') h xl c);
  }
}

#pop-options

ghost fn cbor_raw_match_aux_share
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_share: I.share_t p)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_aux pp p pm xl xh
ensures cbor_raw_match_aux pp p (pm /. 2.0R) xl xh **
        cbor_raw_match_aux pp p (pm /. 2.0R) xl xh
{
  unfold (cbor_raw_match_aux pp p pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp pm)
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
    (cbor_raw_match_content p pp (pm /. 2.0R))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp (pm /. 2.0R)))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux pp p (pm /. 2.0R) xl (Ghost.reveal xh));
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
    (cbor_raw_match_content p pp (pm /. 2.0R))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp (pm /. 2.0R)))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux pp p (pm /. 2.0R) xl (Ghost.reveal xh));
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
requires cbor_raw_match_aux pp p pm xl xh **
         cbor_raw_match_aux pp p pm' xl xh'
ensures cbor_raw_match_aux pp p (pm +. pm') xl xh **
        pure (xh == xh')
{
  unfold (cbor_raw_match_aux pp p pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp pm)
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  unfold (cbor_raw_match_aux pp p pm' xl xh');
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp pm'))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh'));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp pm')
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
  // From sq1 and sq2: Some h1 == Some h2, so h1 == h2 (SMT).
  // Rewrite second content's header from h2 to h1.
  rewrite (cbor_raw_match_content p pp pm'
             (dfst (synth_raw_data_item_recip (Ghost.reveal xh')))
             xl
             (dsnd (synth_raw_data_item_recip (Ghost.reveal xh'))))
       as (cbor_raw_match_content p pp pm'
             (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
             xl
             (dsnd (synth_raw_data_item_recip (Ghost.reveal xh'))));
  cbor_raw_match_content_gather p p_gather pp
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
    xl pm
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
    pm'
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh')));
  // content_gather gives:
  //   cbor_raw_match_content ... (pm +. pm') xh h xl c1 ** pure (c1 == c2)
  // From h1 == h2 (headers equal) and c1 == c2 (content equal):
  //   synth_raw_data_item_recip xh == synth_raw_data_item_recip xh'
  // By synth_raw_data_item_recip_inverse + injectivity: xh == xh'
  // Fold the result
  intro_pure the_prop1 sq1;
  rewrite (pure the_prop1)
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p pp (pm +. pm'))
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p pp (pm +. pm')))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux pp p (pm +. pm') xl (Ghost.reveal xh));
  // Derive xh == xh' from c1 == c2 and h1 == h2
  let c_eq = elim_pure_explicit
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)) ==
     dsnd (synth_raw_data_item_recip (Ghost.reveal xh')));
  intro_pure (Ghost.reveal xh == Ghost.reveal xh') ();
}

(* ========== cbor_raw_match_aux_change ========== *)
(* Changes the recursive sub-match relation p1 to p2 in cbor_raw_match_aux,
   given a ghost function that converts p1 into p2 for all arguments.
   In the typical use case with vmatch_with_perm_guard, the caller only needs to handle
   y' << xh since outside that guard, both p1 and p2 collapse to pure False. *)

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

ghost fn cbor_map_entry_match_change
  (p1 p2: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_change: (x': cbor_raw) -> (pm': perm) -> (y': raw_data_item) ->
    stt_ghost unit emp_inames (p1 pm' x' y') (fun _ -> p2 pm' x' y'))
  (entry: cbor_map_entry cbor_raw)
  (pm: perm)
  (pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_match p1 pm entry pair
ensures cbor_map_entry_match p2 pm entry pair
{
  unfold (cbor_map_entry_match p1 pm entry pair);
  unfold (vmatch_pair_with_proj (p1 pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p1 pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (p1 pm) cbor_map_entry_value_proj entry (snd pair));
  rewrite (p1 pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (p1 pm entry.cbor_map_entry_key (fst pair));
  rewrite (p1 pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (p1 pm entry.cbor_map_entry_value (snd pair));
  p_change entry.cbor_map_entry_key pm (fst pair);
  p_change entry.cbor_map_entry_value pm (snd pair);
  rewrite (p2 pm entry.cbor_map_entry_key (fst pair))
       as (p2 pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (p2 pm entry.cbor_map_entry_value (snd pair))
       as (p2 pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (p2 pm) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (p2 pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (p2 pm) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match p2 pm entry pair);
}

ghost fn cbor_raw_match_content_change
  (p1 p2: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_change: (x': cbor_raw) -> (pm': perm) -> (y': raw_data_item) ->
    stt_ghost unit emp_inames (p1 pm' x' y') (fun _ -> p2 pm' x' y'))
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (pm: perm)
  (c: content h)
requires cbor_raw_match_content p1 pp pm h xl c
ensures cbor_raw_match_content p2 pp pm h xl c
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite (cbor_raw_match_content p1 pp pm h xl c)
       as (cbor_raw_match_content p1 pp pm (| b, la |) xl c);
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) {
    match xl {
      CBOR_Case_String v -> {
        cbor_raw_match_content_eq_string p1 pp pm b la v c;
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_String v) c)
             as (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        cbor_raw_match_content_eq_string p2 pp pm b la v c;
        rewrite (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_String v) c);
        rewrite (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_String v) c)
             as (cbor_raw_match_content p2 pp pm h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_array) {
    match xl {
      CBOR_Case_Array v -> {
        cbor_raw_match_content_eq_array p1 pp pm b la v c;
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p1 pm' elem x)
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        I.mixed_list_match_weaken
          (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p1 pm' elem x)
          (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p2 pm' elem x)
          (fun (x1: cbor_raw) (pm': perm) (x2: raw_data_item) -> p_change x1 pm' x2)
          pp
          v.cbor_array_ptr;
        cbor_raw_match_content_eq_array p2 pp pm b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p2 pm' elem x)
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Array v) c);
        rewrite (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (cbor_raw_match_content p2 pp pm h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_map) {
    match xl {
      CBOR_Case_Map v -> {
        cbor_raw_match_content_eq_map p1 pp pm b la v c;
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Map v) c)
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p1 pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        I.mixed_list_match_weaken
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
               (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match p1 pm' elem x)
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
               (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match p2 pm' elem x)
          (fun (x1: cbor_map_entry cbor_raw) (pm': perm)
               (x2: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match_change p1 p2 p_change x1 pm' x2)
          (nondep_then pp pp)
          v.cbor_map_ptr;
        cbor_raw_match_content_eq_map p2 pp pm b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p2 pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Map v) c);
        rewrite (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Map v) c)
             as (cbor_raw_match_content p2 pp pm h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_tagged) {
    match xl {
      CBOR_Case_Tagged v -> {
        cbor_raw_match_content_eq_tagged p1 pp pm b la v c;
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_tagged_content_slprop p1 pm v (content_as_raw_data_item b la c));
        unfold (cbor_tagged_content_slprop p1 pm v (content_as_raw_data_item b la c));
        unfold (vmatch_ref
          (fun (vl: cbor_raw) (vh: raw_data_item) -> p1 (pm *. v.cbor_tagged_payload_perm) vl vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
          p1 (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        p_change vl (pm *. v.cbor_tagged_payload_perm) (content_as_raw_data_item b la c);
        fold (vmatch_ref
          (fun (vl': cbor_raw) (vh: raw_data_item) -> p2 (pm *. v.cbor_tagged_payload_perm) vl' vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        fold (cbor_tagged_content_slprop p2 pm v (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged p2 pp pm b la v c;
        rewrite (cbor_tagged_content_slprop p2 pm v (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Tagged v) c);
        rewrite (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_raw_match_content p2 pp pm h xl c);
      }
      CBOR_Case_Tagged_Serialized v -> {
        cbor_raw_match_content_eq_tagged_serialized p1 pp pm b la v c;
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged_serialized p2 pp pm b la v c;
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
             as (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c);
        rewrite (cbor_raw_match_content p2 pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (cbor_raw_match_content p2 pp pm h xl c);
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content p1 pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else {
    cbor_raw_match_content_eq_other p1 pp pm b la xl c;
    rewrite (cbor_raw_match_content p1 pp pm (| b, la |) xl c) as emp;
    cbor_raw_match_content_eq_other p2 pp pm b la xl c;
    rewrite emp as (cbor_raw_match_content p2 pp pm (| b, la |) xl c);
    rewrite (cbor_raw_match_content p2 pp pm (| b, la |) xl c)
         as (cbor_raw_match_content p2 pp pm h xl c);
  }
}

ghost fn cbor_raw_match_aux_change
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (p1 p2: perm -> cbor_raw -> raw_data_item -> slprop)
  (p_change: (x': cbor_raw) -> (pm': perm) -> (y': raw_data_item) ->
    stt_ghost unit emp_inames (p1 pm' x' y') (fun _ -> p2 pm' x' y'))
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_aux pp p1 pm xl xh
ensures cbor_raw_match_aux pp p2 pm xl xh
{
  unfold (cbor_raw_match_aux pp p1 pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p1 pp pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content p1 pp pm)
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
  cbor_raw_match_content_change p1 p2 p_change pp
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
    xl pm
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)));
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
    (cbor_raw_match_content p2 pp pm)
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content p2 pp pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux pp p2 pm xl (Ghost.reveal xh));
}

#pop-options

let cbor_raw_match :
  (pm: perm) ->
  (xl: cbor_raw) ->
  (xh: raw_data_item) ->
  Tot slprop
= vmatch_with_perm_rec (cbor_raw_match_aux parse_raw_data_item)

let cbor_raw_match_eq
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Lemma (cbor_raw_match pm xl xh == cbor_raw_match_aux parse_raw_data_item (vmatch_with_perm_guard xh cbor_raw_match) pm xl xh)
= assert_norm (cbor_raw_match == vmatch_with_perm_rec (cbor_raw_match_aux parse_raw_data_item));
  vmatch_with_perm_rec_eq (cbor_raw_match_aux parse_raw_data_item) pm xl xh
