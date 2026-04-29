module CBOR.Pulse.Raw.EverParse.Read
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Type
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.EverParse.Match
open LowParse.Pulse.Base
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Base
open LowParse.PulseParse.Combinators
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
module Trade = Pulse.Lib.Trade.Util
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base

(* The content zero_copy_parse_strong_prefix for each header case.
   Given a header h and input slice with pts_to_parsed_strong_prefix (parse_content pp h),
   produce a cbor_raw value with the appropriate match relation.
   
   Note: the permission on the input slice (from zero_copy_parse_strong_prefix) is the
   same as pm at the call site (from dtuple2_with_proj). We use pm in the content
   relation and the same pm comes through as the slice permission. *)

(* Helper to construct the proper cbor_raw for the "other" case (int or simple_value).
   This is a total function so it can be used inside Pulse without splitting the resource context. *)
inline_for_extraction
let cbor_raw_read_other
  (b: initial_byte)
  (la: long_argument b)
: Pure cbor_raw
    (requires
      b.major_type <> cbor_major_type_byte_string /\
      b.major_type <> cbor_major_type_text_string /\
      b.major_type <> cbor_major_type_array /\
      b.major_type <> cbor_major_type_map /\
      b.major_type <> cbor_major_type_tagged)
    (ensures fun _ -> True)
= if b.major_type = cbor_major_type_simple_value
  then CBOR_Case_Simple (argument_as_simple_value b la)
  else CBOR_Case_Int ({
    cbor_int_type = b.major_type;
    cbor_int_size = (argument_as_raw_uint64 b la).size;
    cbor_int_value = (argument_as_raw_uint64 b la).value;
  })

(* Lemma: if pts_to_parsed_strong_prefix_prop holds for parse_content in the string case,
   then the slice length >= argument n AND v == Seq.slice w 0 n. *)
#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let string_parse_content_length_lemma
  (pp: parser parse_raw_data_item_kind raw_data_item)
  (b: initial_byte)
  (la: long_argument b)
  (w: Seq.seq byte)
  (v: content (| b, la |))
  (_: squash (b.major_type = cbor_major_type_byte_string \/ b.major_type = cbor_major_type_text_string))
  (_: squash (PPB.pts_to_parsed_strong_prefix_prop (parse_content pp (| b, la |)) w v))
: Lemma (U64.v (argument_as_uint64 b la) <= Seq.length w /\
         (v <: Seq.seq byte) == Seq.slice w 0 (U64.v (argument_as_uint64 b la)))
= let n = U64.v (argument_as_uint64 b la) in
  let pred = lseq_utf8_correct b.major_type n in
  parse_filter_eq (LowParse.Spec.SeqBytes.parse_lseq_bytes n) pred w;
  assert_norm (forall (s: bytes) (sz: nat) . parse (LowParse.Spec.SeqBytes.tot_parse_lseq_bytes sz) s ==
    (if Seq.length s < sz then None else Some (Seq.slice s 0 sz, sz)))
#pop-options

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_raw_read_content
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (pp: parser parse_raw_data_item_kind raw_data_item)
  (pm: perm)
  (f64: squash SZ.fits_u64)
  (h: header)
: PPB.zero_copy_parse_strong_prefix #cbor_raw #(content h)
    (vmatch_dep_pair_with_proj_content
      cbor_raw_match_header cbor_raw_id_proj
      (cbor_raw_match_content p pp pm) h)
    #parse_content_kind
    (parse_content pp h)
= (input: S.slice byte)
  (#pms: perm)
  (#v: Ghost.erased (content h))
{
  let b = dfst h;
  let la = dsnd h;
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) {
    // String case: content is parse_filter (parse_lseq_bytes n) utf8
    let n = SZ.uint64_to_sizet (argument_as_uint64 b la);
    header_eta h;
    // Elim pts_to_parsed_strong_prefix to get raw slice bytes
    PPB.pts_to_parsed_strong_prefix_elim input;
    with w . assert (S.pts_to input #pms w);
    // Extract the parsing property and derive length bound
    Pulse.Lib.Core.elim_pure_explicit (PPB.pts_to_parsed_strong_prefix_prop (parse_content pp (| b, la |)) w (Ghost.reveal v));
    string_parse_content_length_lemma pp b la w (Ghost.reveal v) () ();
    let input1_input2 = Pulse.Lib.Slice.Util.split_trade input #pms n #w;
    match input1_input2 {
      input1, input2 -> {
    with wb1 . assert (S.pts_to input1 #pms wb1);
    with wb2 . assert (S.pts_to input2 #pms wb2);
    // Drop the second part, keeping the trade
    Trade.elim_hyp_r
      (S.pts_to input1 #pms wb1)
      (S.pts_to input2 #pms wb2)
      (S.pts_to input #pms w);
    // Chain trade: pts_to input1 -> pts_to input -> pts_to_parsed_strong_prefix
    Trade.trans
      (S.pts_to input1 #pms wb1)
      (S.pts_to input #pms w)
      (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v);
    // Construct the string result
    S.pts_to_len input1;
    let res = CBOR_Case_String ({
      cbor_string_type = b.major_type;
      cbor_string_size = (argument_as_raw_uint64 b la).size;
      cbor_string_ptr = input1;
      cbor_string_perm = pms /. pm;
    });
    // Establish the match content: S.pts_to input1 #(pm *. (pms/pm)) c
    rewrite (S.pts_to input1 #pms wb1)
      as (cbor_raw_match_content p pp pm h res (Ghost.reveal v));
    fold (cbor_raw_match_header res h);
    fold (vmatch_dep_pair_with_proj_content
      cbor_raw_match_header cbor_raw_id_proj
      (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
    // Trade back
    intro
      (Trade.trade
        (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v))
        (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      #(Trade.trade
          (S.pts_to input1 #pms wb1)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      fn _ {
        unfold (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
        unfold (cbor_raw_match_header res h);
        drop_ (pure (cbor_raw_get_header res == Some h));
        rewrite (cbor_raw_match_content p pp pm h res (Ghost.reveal v))
          as (S.pts_to input1 #pms wb1);
        Trade.elim
          (S.pts_to input1 #pms wb1)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v)
      };
    res
    }
    }
  } else if (b.major_type = cbor_major_type_array) {
    // Array case: content is weaken _ (parse_nlist n pp)
    let n = SZ.uint64_to_sizet (argument_as_uint64 b la);
    PPB.pts_to_parsed_strong_prefix_ext_trade (parse_nlist (SZ.v n) pp) input;
    let res = CBOR_Case_Array ({
      cbor_array_length_size = (argument_as_raw_uint64 b la).size;
      cbor_array_ptr = I.Base (I.Serialized (pms /. pm) n input);
      cbor_array_slice_perm = 1.0R;
    });
    // content h = nlist (U64.v ...) raw_data_item = list raw_data_item in this branch
    header_eta h;
    let vl : Ghost.erased (list raw_data_item) = Ghost.hide (content_as_list_raw b la (Ghost.reveal v));
    rewrite (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #pms v)
      as (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #(pm *. (pms /. pm)) (Ghost.reveal vl));
    intro_pure ((Ghost.reveal vl <: list raw_data_item) == Ghost.reveal vl) ();
    fold (I.base_iterator_match
      (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
      pp pm (I.Serialized (pms /. pm) n input) (Ghost.reveal vl));
    fold (I.iterator_match
      (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
      pp (pm *. 1.0R)
      (I.Base (I.Serialized (pms /. pm) n input))
      (Ghost.reveal vl));
    rewrite (I.iterator_match
      (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
      pp (pm *. 1.0R) (I.Base (I.Serialized (pms /. pm) n input)) (Ghost.reveal vl))
      as (cbor_raw_match_content p pp pm h res (Ghost.reveal v));
    fold (cbor_raw_match_header res h);
    fold (vmatch_dep_pair_with_proj_content
      cbor_raw_match_header cbor_raw_id_proj
      (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
    intro
      (Trade.trade
        (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v))
        (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      #(Trade.trade
          (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      fn _ {
        unfold (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
        unfold (cbor_raw_match_header res h);
        drop_ (pure (cbor_raw_get_header res == Some h));
        rewrite (cbor_raw_match_content p pp pm h res (Ghost.reveal v))
          as (I.iterator_match
            (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
            pp (pm *. 1.0R) (I.Base (I.Serialized (pms /. pm) n input)) (Ghost.reveal vl));
        unfold (I.iterator_match
          (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
          pp (pm *. 1.0R) (I.Base (I.Serialized (pms /. pm) n input)) (Ghost.reveal vl));
        unfold (I.base_iterator_match
          (fun (pm': perm) (elem: cbor_raw) (x: raw_data_item) -> p pm' elem x)
          pp pm (I.Serialized (pms /. pm) n input) (Ghost.reveal vl));
        with l' . assert (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #(pm *. (pms /. pm)) l');
        drop_ (pure ((l' <: list raw_data_item) == Ghost.reveal vl));
        rewrite (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #(pm *. (pms /. pm)) l')
          as (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #pms v);
        Trade.elim
          (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) pp) input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v)
      };
    res
  } else if (b.major_type = cbor_major_type_map) {
    // Map case: content is weaken _ (parse_nlist n (nondep_then pp pp))
    let n = SZ.uint64_to_sizet (argument_as_uint64 b la);
    PPB.pts_to_parsed_strong_prefix_ext_trade (parse_nlist (SZ.v n) (nondep_then pp pp)) input;
    let res = CBOR_Case_Map ({
      cbor_map_length_size = (argument_as_raw_uint64 b la).size;
      cbor_map_ptr = I.Base (I.Serialized (pms /. pm) n input);
      cbor_map_slice_perm = 1.0R;
    });
    header_eta h;
    let vl : Ghost.erased (list (raw_data_item & raw_data_item)) = Ghost.hide (content_as_list_pair b la (Ghost.reveal v));
    rewrite (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #pms v)
      as (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #(pm *. (pms /. pm)) (Ghost.reveal vl));
    intro_pure ((Ghost.reveal vl <: list (raw_data_item & raw_data_item)) == Ghost.reveal vl) ();
    fold (I.base_iterator_match
      (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match p pm' elem x)
      (nondep_then pp pp) pm (I.Serialized (pms /. pm) n input) (Ghost.reveal vl));
    fold (I.iterator_match
      (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match p pm' elem x)
      (nondep_then pp pp) (pm *. 1.0R)
      (I.Base (I.Serialized (pms /. pm) n input))
      (Ghost.reveal vl));
    rewrite (I.iterator_match
      (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match p pm' elem x)
      (nondep_then pp pp) (pm *. 1.0R) (I.Base (I.Serialized (pms /. pm) n input)) (Ghost.reveal vl))
      as (cbor_raw_match_content p pp pm h res (Ghost.reveal v));
    fold (cbor_raw_match_header res h);
    fold (vmatch_dep_pair_with_proj_content
      cbor_raw_match_header cbor_raw_id_proj
      (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
    intro
      (Trade.trade
        (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v))
        (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      #(Trade.trade
          (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      fn _ {
        unfold (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
        unfold (cbor_raw_match_header res h);
        drop_ (pure (cbor_raw_get_header res == Some h));
        rewrite (cbor_raw_match_content p pp pm h res (Ghost.reveal v))
          as (I.iterator_match
            (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match p pm' elem x)
            (nondep_then pp pp) (pm *. 1.0R) (I.Base (I.Serialized (pms /. pm) n input)) (Ghost.reveal vl));
        unfold (I.iterator_match
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match p pm' elem x)
          (nondep_then pp pp) (pm *. 1.0R) (I.Base (I.Serialized (pms /. pm) n input)) (Ghost.reveal vl));
        unfold (I.base_iterator_match
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw) (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match p pm' elem x)
          (nondep_then pp pp) pm (I.Serialized (pms /. pm) n input) (Ghost.reveal vl));
        with l' . assert (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #(pm *. (pms /. pm)) l');
        drop_ (pure ((l' <: list (raw_data_item & raw_data_item)) == Ghost.reveal vl));
        rewrite (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #(pm *. (pms /. pm)) l')
          as (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #pms v);
        Trade.elim
          (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n) (nondep_then pp pp)) input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v)
      };
    res
  } else if (b.major_type = cbor_major_type_tagged) {
    // Tagged case: content is weaken _ pp, match is pts_to_parsed_strong_prefix pp
    // Convert weaken _ pp to pp via ext_trade
    PPB.pts_to_parsed_strong_prefix_ext_trade pp input;
    // Now we have: pts_to_parsed_strong_prefix pp input #pms v
    //   + trade back to pts_to_parsed_strong_prefix (parse_content pp h) input #pms v
    let res = CBOR_Case_Tagged_Serialized ({
      cbor_tagged_serialized_tag = argument_as_raw_uint64 b la;
      cbor_tagged_serialized_ptr = input;
      cbor_tagged_serialized_slice_perm = pms /. pm;
    });
    // Need to show: vmatch_dep_pair_with_proj_content ... h res v
    //   = cbor_raw_match_header res h ** cbor_raw_match_content p pp pm h res v
    // cbor_raw_match_content ... = pts_to_parsed_strong_prefix pp input #(pm *. (pms /. pm)) v
    //   = pts_to_parsed_strong_prefix pp input #pms v  (by arithmetic: pm * (pms/pm) = pms)
    // cbor_raw_match_header res h = pure (cbor_raw_get_header res == Some h)
    rewrite (PPB.pts_to_parsed_strong_prefix pp input #pms v)
      as (PPB.pts_to_parsed_strong_prefix pp input #(pm *. (pms /. pm)) (Ghost.reveal v));
    rewrite (PPB.pts_to_parsed_strong_prefix pp input #(pm *. (pms /. pm)) (Ghost.reveal v))
      as (cbor_raw_match_content p pp pm h res (Ghost.reveal v));
    fold (cbor_raw_match_header res h);
    fold (vmatch_dep_pair_with_proj_content
      cbor_raw_match_header cbor_raw_id_proj
      (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
    // Now set up the trade back
    intro
      (Trade.trade
        (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v))
        (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      #(Trade.trade
          (PPB.pts_to_parsed_strong_prefix pp input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      fn _ {
        unfold (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
        unfold (cbor_raw_match_header res h);
        drop_ (pure (cbor_raw_get_header res == Some h));
        rewrite (cbor_raw_match_content p pp pm h res (Ghost.reveal v))
          as (PPB.pts_to_parsed_strong_prefix pp input #(pm *. (pms /. pm)) (Ghost.reveal v));
        rewrite (PPB.pts_to_parsed_strong_prefix pp input #(pm *. (pms /. pm)) (Ghost.reveal v))
          as (PPB.pts_to_parsed_strong_prefix pp input #pms v);
        Trade.elim _ _
      };
    res
  } else {
    // Other case (int / simple): content is parse_empty, relation is emp
    // Need proper cbor_raw matching the header
    PPB.pts_to_parsed_strong_prefix_ext_trade parse_empty input;
    header_eta h;
    let res : cbor_raw =
      cbor_raw_read_other b la;
    // cbor_raw_match_content is emp in this branch
    rewrite emp as (cbor_raw_match_content p pp pm h res (Ghost.reveal v));
    fold (cbor_raw_match_header res h);
    fold (vmatch_dep_pair_with_proj_content
      cbor_raw_match_header cbor_raw_id_proj
      (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
    // Trade: from vmatch back to pts_to_parsed_strong_prefix
    intro
      (Trade.trade
        (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v))
        (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      #(PPB.pts_to_parsed_strong_prefix parse_empty input #pms v **
        Trade.trade
          (PPB.pts_to_parsed_strong_prefix parse_empty input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v))
      fn _ {
        unfold (vmatch_dep_pair_with_proj_content
          cbor_raw_match_header cbor_raw_id_proj
          (cbor_raw_match_content p pp pm) h res (Ghost.reveal v));
        unfold (cbor_raw_match_header res h);
        drop_ (pure (cbor_raw_get_header res == Some h));
        rewrite (cbor_raw_match_content p pp pm h res (Ghost.reveal v)) as emp;
        Trade.elim
          (PPB.pts_to_parsed_strong_prefix parse_empty input #pms v)
          (PPB.pts_to_parsed_strong_prefix (parse_content pp h) input #pms v)
      };
    res
  }
}

#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"

module V = CBOR.Pulse.Raw.EverParse.Validate

inline_for_extraction
let cbor_raw_read_aux
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (pp: parser parse_raw_data_item_kind raw_data_item)
  (pm: perm)
  (f64: squash SZ.fits_u64)
: PPB.zero_copy_parse_strong_prefix #cbor_raw #raw_data_item
    (cbor_raw_match_aux p pp pm)
    #parse_raw_data_item_kind
    (parse_raw_data_item_aux pp)
= zero_copy_parse_strong_prefix_synth
    (read_and_zero_copy_parse_strong_prefix_dtuple2_with_proj
      cbor_raw_match_header
      cbor_raw_id_proj
      (cbor_raw_match_content p pp pm)
      (V.jump_header ())
      (PPB.leaf_reader_of_serialized (V.read_header ()))
      ()
      (fun h -> cbor_raw_read_content p pp pm f64 h))
    synth_raw_data_item
    synth_raw_data_item_recip
    ()

#pop-options
