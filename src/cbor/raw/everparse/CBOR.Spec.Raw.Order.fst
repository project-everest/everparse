module CBOR.Spec.Raw.Order
module F = CBOR.Spec.Raw.Format
module M = CBOR.Spec.Raw.Map
module LP = LowParse.Spec.Base

let serialize_cbor c = F.serialize_raw_data_item c

let serialize_cbor_inj c1 c2 s1 s2 =
  LP.serialize_strong_prefix #F.parse_raw_data_item_kind #_ #F.parse_raw_data_item F.serialize_raw_data_item c1 c2 s1 s2

let serialize_cbor_nonempty c =
  LP.tot_serialize_length F.serialize_raw_data_item c

let deterministically_encoded_cbor_map_key_order = F.deterministically_encoded_cbor_map_key_order

let deterministically_encoded_cbor_map_key_order_irrefl x =
  Classical.move_requires (F.deterministically_encoded_cbor_map_key_order_irrefl x) x

let deterministically_encoded_cbor_map_key_order_trans x y z =
  F.deterministically_encoded_cbor_map_key_order_trans x y z

let deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 ext =
  assert_norm (map_entry_order deterministically_encoded_cbor_map_key_order raw_data_item == LowParse.Spec.Assoc.map_entry_order F.deterministically_encoded_cbor_map_key_order raw_data_item);
 F.deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 (fun k ->
  LowParse.Spec.Assoc.list_ghost_assoc_eq k m1;
  LowParse.Spec.Assoc.list_ghost_assoc_eq k m2;
  ext k)

let list_sorted_map_entry_order_deterministically_encoded_cbor_map_key_order_no_repeats
  (#t: Type)
  (l: list (raw_data_item & t))
: Lemma
  (requires (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))
= assert_norm (map_entry_order deterministically_encoded_cbor_map_key_order raw_data_item == LowParse.Spec.Assoc.map_entry_order F.deterministically_encoded_cbor_map_key_order raw_data_item);
  M.list_sorted_map_entry_order_no_repeats deterministically_encoded_cbor_map_key_order l

let rec bytes_lex_compare_correct
  (s1 s2: Seq.seq U8.t)
: Lemma
  (ensures (bytes_lex_compare s1 s2 == LowParse.Spec.SeqBytes.bytes_lex_compare s1 s2))
  (decreases (Seq.length s1))
  [SMTPat (bytes_lex_compare s1 s2)]
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then ()
  else begin
    Seq.cons_head_tail s1;
    Seq.cons_head_tail s2;
    bytes_lex_compare_correct (Seq.tail s1) (Seq.tail s2)
  end

let bytes_lex_compare_equal
  x1 x2
= LowParse.Spec.Sorted.lex_compare_equal
    LowParse.Spec.SeqBytes.byte_compare
    (fun _ _ -> ())
    (Seq.seq_to_list x1)
    (Seq.seq_to_list x2);
  Seq.lemma_seq_list_bij x1;
  Seq.lemma_seq_list_bij x2

let deterministically_encoded_cbor_map_key_order_spec
  x1 x2
= ()

#push-options "--z3rlimit 32"

#restart-solver
let rec cbor_compare_correct'
  (x1 x2: raw_data_item)
: Lemma
  (ensures (cbor_compare x1 x2 == bytes_lex_compare (serialize_cbor x1) (serialize_cbor x2)))
  (decreases x1)
= let ty1 = get_major_type x1 in
  if LowParse.Spec.SeqBytes.byte_compare (get_major_type x1) (get_major_type x2) <> 0
  then F.serialized_lex_compare_major_type_intro x1 x2
  else if ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64
  then F.serialized_lex_compare_int64 ty1 (Int64?.v x1) (Int64?.v x2)
  else if ty1 = cbor_major_type_simple_value
  then F.serialized_lex_compare_simple_value (Simple?.v x1) (Simple?.v x2)
  else if ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string
  then F.serialized_lex_compare_string ty1 (String?.len x1) (String?.v x1) (String?.len x2) (String?.v x2)
  else if ty1 = cbor_major_type_tagged
  then begin
    F.serialized_lex_compare_tagged (Tagged?.tag x1) (Tagged?.v x1) (Tagged?.tag x2) (Tagged?.v x2);
    cbor_compare_correct' (Tagged?.v x1) (Tagged?.v x2)
  end
  else if ty1 = cbor_major_type_array
  then begin
    F.serialized_lex_compare_array (Array?.len x1) (Array?.v x1) (Array?.len x2) (Array?.v x2);
    if List.Tot.length (Array?.v x1) = List.Tot.length (Array?.v x2)
    then cbor_compare_array_correct (Array?.v x1) (Array?.v x2)
  end
  else if ty1 = cbor_major_type_map
  then begin
    F.serialized_lex_compare_map (Map?.len x1) (Map?.v x1) (Map?.len x2) (Map?.v x2);
    if List.Tot.length (Map?.v x1) = List.Tot.length (Map?.v x2)
    then cbor_compare_map_correct (Map?.v x1) (Map?.v x2)
  end
  else assert False

and cbor_compare_array_correct
  (x1 x2: list raw_data_item)
: Lemma
  (requires (List.Tot.length x1 == List.Tot.length x2))
  (ensures (cbor_compare_array x1 x2 == LowParse.Spec.Sorted.lex_compare (F.serialized_lex_compare F.serialize_raw_data_item) x1 x2))
  (decreases x1)
= match x1, x2 with
  | a1 :: q1, a2 :: q2 ->
    cbor_compare_correct' a1 a2;
    cbor_compare_array_correct q1 q2
  | _ -> ()

and cbor_compare_map_correct
  (x1 x2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (List.Tot.length x1 == List.Tot.length x2))
  (ensures (cbor_compare_map x1 x2 == LowParse.Spec.Sorted.lex_compare (F.serialized_lex_compare (LowParse.Spec.Combinators.tot_serialize_nondep_then F.serialize_raw_data_item F.serialize_raw_data_item)) x1 x2))
  (decreases x1)
= match x1, x2 with
  | a1 :: q1, a2 :: q2 ->
    cbor_compare_correct' (fst a1) (fst a2);
    cbor_compare_correct' (snd a1) (snd a2);
    F.serialized_lex_compare_nondep_then F.serialize_raw_data_item F.serialize_raw_data_item a1 a2;
    cbor_compare_map_correct q1 q2
  | _ -> ()

#pop-options

let cbor_compare_correct = cbor_compare_correct'
