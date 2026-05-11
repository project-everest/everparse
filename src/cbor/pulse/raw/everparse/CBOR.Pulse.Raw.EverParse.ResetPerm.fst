module CBOR.Pulse.Raw.EverParse.ResetPerm

open CBOR.Spec.Raw.EverParse
open LowParse.Pulse.Base
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Base
open LowParse.PulseParse.Projectors
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
module Trade = Pulse.Lib.Trade
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match

let cbor_raw_reset_perm_tot (f: perm) (c: cbor_raw) : cbor_raw =
  match c with
  | CBOR_Case_String v -> CBOR_Case_String { v with cbor_string_perm = f *. v.cbor_string_perm }
  | CBOR_Case_Tagged v -> CBOR_Case_Tagged { v with
      cbor_tagged_ref_perm = f *. v.cbor_tagged_ref_perm;
      cbor_tagged_payload_perm = f *. v.cbor_tagged_payload_perm }
  | CBOR_Case_Tagged_Serialized v -> CBOR_Case_Tagged_Serialized { v with
      cbor_tagged_serialized_slice_perm = f *. v.cbor_tagged_serialized_slice_perm }
  | CBOR_Case_Array v -> CBOR_Case_Array { v with cbor_array_slice_perm = f *. v.cbor_array_slice_perm }
  | CBOR_Case_Map v -> CBOR_Case_Map { v with cbor_map_slice_perm = f *. v.cbor_map_slice_perm }
  | _ -> c

let perm_q_p_r (q p r: perm) : Lemma (q *. ((p /. q) *. r) == p *. r) = ()

let cbor_raw_get_header_reset_perm (f: perm) (c: cbor_raw)
  : Lemma (cbor_raw_get_header (cbor_raw_reset_perm_tot f c) == cbor_raw_get_header c)
= ()

#push-options "--z3rlimit 64"
let cbor_raw_reset_perm_tot_inv (p q: perm) (c: cbor_raw)
  : Lemma (cbor_raw_reset_perm_tot (q /. p) (cbor_raw_reset_perm_tot (p /. q) c) == c)
= ()
#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_content_reset_perm
  (p: perm -> cbor_raw -> raw_data_item -> slprop)
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (pm q: perm)
  (h: header)
  (xl: cbor_raw)
  (c: content h)
requires cbor_raw_match_content p pp pm h xl c
ensures cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite (cbor_raw_match_content p pp pm h xl c)
       as (cbor_raw_match_content p pp pm (| b, la |) xl c);
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) {
    match xl {
      CBOR_Case_String v -> {
        let v' : cbor_string = { v with cbor_string_perm = (pm /. q) *. v.cbor_string_perm };
        cbor_raw_match_content_eq_string p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_String v) c)
             as (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        perm_q_p_r q pm v.cbor_string_perm;
        rewrite (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (S.pts_to v'.cbor_string_ptr #(q *. v'.cbor_string_perm) (content_as_seq_u8 b la c));
        cbor_raw_match_content_eq_string p pp q b la v' c;
        rewrite (S.pts_to v'.cbor_string_ptr #(q *. v'.cbor_string_perm) (content_as_seq_u8 b la c))
             as (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_String v') c);
        rewrite (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_String v') c)
             as (cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c);
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
        let v' : cbor_array cbor_raw = { v with cbor_array_slice_perm = (pm /. q) *. v.cbor_array_slice_perm };
        cbor_raw_match_content_eq_array p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (I.mixed_list_match p pp (pm *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c));
        perm_q_p_r q pm v.cbor_array_slice_perm;
        rewrite (I.mixed_list_match p pp (pm *. v.cbor_array_slice_perm) v.cbor_array_ptr (content_as_list_raw b la c))
             as (I.mixed_list_match p pp (q *. v'.cbor_array_slice_perm) v'.cbor_array_ptr (content_as_list_raw b la c));
        cbor_raw_match_content_eq_array p pp q b la v' c;
        rewrite (I.mixed_list_match p pp (q *. v'.cbor_array_slice_perm) v'.cbor_array_ptr (content_as_list_raw b la c))
             as (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Array v') c);
        rewrite (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Array v') c)
             as (cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c);
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
        let v' : cbor_map cbor_raw = { v with cbor_map_slice_perm = (pm /. q) *. v.cbor_map_slice_perm };
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
        perm_q_p_r q pm v.cbor_map_slice_perm;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   (q *. v'.cbor_map_slice_perm)
                   v'.cbor_map_ptr
                   (content_as_list_pair b la c));
        cbor_raw_match_content_eq_map p pp q b la v' c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match p pm' elem x)
                   (nondep_then pp pp)
                   (q *. v'.cbor_map_slice_perm)
                   v'.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Map v') c);
        rewrite (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Map v') c)
             as (cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c);
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
        let v' : cbor_tagged cbor_raw = { v with
          cbor_tagged_ref_perm = (pm /. q) *. v.cbor_tagged_ref_perm;
          cbor_tagged_payload_perm = (pm /. q) *. v.cbor_tagged_payload_perm
        };
        let cr = content_as_raw_data_item b la c;
        cbor_raw_match_content_eq_tagged p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_tagged_content_slprop p pm v cr);
        unfold (cbor_tagged_content_slprop p pm v cr);
        unfold (vmatch_ref
          (fun (vl: cbor_raw) (vh: raw_data_item) -> p (pm *. v.cbor_tagged_payload_perm) vl vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          cr);
        with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
          p (pm *. v.cbor_tagged_payload_perm) vl cr);
        perm_q_p_r q pm v.cbor_tagged_ref_perm;
        perm_q_p_r q pm v.cbor_tagged_payload_perm;
        rewrite each
          (pm *. v.cbor_tagged_ref_perm) as (q *. v'.cbor_tagged_ref_perm);
        rewrite each
          (pm *. v.cbor_tagged_payload_perm) as (q *. v'.cbor_tagged_payload_perm);
        rewrite (R.pts_to v.cbor_tagged_ptr #(q *. v'.cbor_tagged_ref_perm) vl)
             as (R.pts_to v'.cbor_tagged_ptr #(q *. v'.cbor_tagged_ref_perm) vl);
        fold (vmatch_ref
          (fun (vl': cbor_raw) (vh: raw_data_item) -> p (q *. v'.cbor_tagged_payload_perm) vl' vh)
          ({ v = v'.cbor_tagged_ptr; p = q *. v'.cbor_tagged_ref_perm })
          cr);
        fold (cbor_tagged_content_slprop p q v' cr);
        cbor_raw_match_content_eq_tagged p pp q b la v' c;
        rewrite (cbor_tagged_content_slprop p q v' cr)
             as (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Tagged v') c);
        rewrite (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Tagged v') c)
             as (cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c);
      }
      CBOR_Case_Tagged_Serialized v -> {
        let v' : cbor_tagged_serialized = { v with
          cbor_tagged_serialized_slice_perm = (pm /. q) *. v.cbor_tagged_serialized_slice_perm
        };
        let cr = content_as_raw_data_item b la c;
        cbor_raw_match_content_eq_tagged_serialized p pp pm b la v c;
        rewrite (cbor_raw_match_content p pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) cr);
        perm_q_p_r q pm v.cbor_tagged_serialized_slice_perm;
        rewrite (pts_to_parsed_strong_prefix pp v.cbor_tagged_serialized_ptr #(pm *. v.cbor_tagged_serialized_slice_perm) cr)
             as (pts_to_parsed_strong_prefix pp v'.cbor_tagged_serialized_ptr #(q *. v'.cbor_tagged_serialized_slice_perm) cr);
        cbor_raw_match_content_eq_tagged_serialized p pp q b la v' c;
        rewrite (pts_to_parsed_strong_prefix pp v'.cbor_tagged_serialized_ptr #(q *. v'.cbor_tagged_serialized_slice_perm) cr)
             as (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Tagged_Serialized v') c);
        rewrite (cbor_raw_match_content p pp q (| b, la |) (CBOR_Case_Tagged_Serialized v') c)
             as (cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c);
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
    cbor_raw_match_content_eq_other p pp q b la (cbor_raw_reset_perm_tot (pm /. q) xl) c;
    rewrite emp as (cbor_raw_match_content p pp q (| b, la |) (cbor_raw_reset_perm_tot (pm /. q) xl) c);
    rewrite (cbor_raw_match_content p pp q (| b, la |) (cbor_raw_reset_perm_tot (pm /. q) xl) c)
         as (cbor_raw_match_content p pp q h (cbor_raw_reset_perm_tot (pm /. q) xl) c);
  }
}
```

```pulse
ghost fn cbor_raw_reset_perm_forward
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
  (q: perm)
requires cbor_raw_match pm xl xh
ensures cbor_raw_match q (cbor_raw_reset_perm_tot (pm /. q) xl) xh
{
  cbor_raw_match_unfold_aux xl;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl (Ghost.reveal xh));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
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
  cbor_raw_match_content_reset_perm
    cbor_raw_match
    parse_raw_data_item
    pm q
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
    xl
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)));
  cbor_raw_get_header_reset_perm (pm /. q) xl;
  intro_pure
    (cbor_raw_get_header (cbor_raw_reset_perm_tot (pm /. q) xl) ==
     Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh))))
    ();
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_reset_perm_tot (pm /. q) xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (cbor_raw_reset_perm_tot (pm /. q) xl)) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get (cbor_raw_reset_perm_tot (pm /. q) xl))
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item q)
    (cbor_raw_reset_perm_tot (pm /. q) xl)
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item q))
    synth_raw_data_item_recip
    (cbor_raw_reset_perm_tot (pm /. q) xl) (Ghost.reveal xh));
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match q (cbor_raw_reset_perm_tot (pm /. q) xl) (Ghost.reveal xh));
  cbor_raw_match_fold_aux (cbor_raw_reset_perm_tot (pm /. q) xl);
}
```

```pulse
ghost fn cbor_raw_reset_perm_correct
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
  (q: perm)
requires cbor_raw_match pm xl xh
ensures cbor_raw_match q (cbor_raw_reset_perm_tot (pm /. q) xl) xh **
  trade (cbor_raw_match q (cbor_raw_reset_perm_tot (pm /. q) xl) xh)
        (cbor_raw_match pm xl xh)
{
  let xl' = Ghost.hide (cbor_raw_reset_perm_tot (pm /. q) xl);
  cbor_raw_reset_perm_forward xl q;
  intro
    (Trade.trade
      (cbor_raw_match q (Ghost.reveal xl') (Ghost.reveal xh))
      (cbor_raw_match pm xl (Ghost.reveal xh)))
    #emp
    fn _ {
      cbor_raw_reset_perm_forward (Ghost.reveal xl') pm;
      cbor_raw_reset_perm_tot_inv pm q xl;
      rewrite each (cbor_raw_reset_perm_tot (q /. pm) (Ghost.reveal xl')) as xl;
    };
  rewrite each (Ghost.reveal xl') as (cbor_raw_reset_perm_tot (pm /. q) xl);
}
```

```pulse
fn cbor_raw_reset_perm
  (pm: perm)
  (c: cbor_raw)
  (#xh: Ghost.erased raw_data_item)
  (q: perm)
requires cbor_raw_match pm c xh
returns c' : cbor_raw
ensures cbor_raw_match q c' xh **
  trade (cbor_raw_match q c' xh) (cbor_raw_match pm c xh)
{
  cbor_raw_reset_perm_correct c q;
  cbor_raw_reset_perm_tot (pm /. q) c
}
```

#pop-options
