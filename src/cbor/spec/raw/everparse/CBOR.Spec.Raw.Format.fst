module CBOR.Spec.Raw.Format
module F = CBOR.Spec.Raw.EverParse
module M = CBOR.Spec.Raw.Map
module LP = LowParse.Spec.Combinators

let serialize_cbor c = F.tot_serialize_raw_data_item c

let serialize_cbor_inj c1 c2 s1 s2 =
  LP.serialize_strong_prefix #F.parse_raw_data_item_kind #_ #F.parse_raw_data_item F.serialize_raw_data_item c1 c2 s1 s2

let parse_cbor x =
  match F.tot_parse_raw_data_item x with
  | None -> None
  | Some (y, n) ->
    LP.serializer_correct_implies_complete #F.parse_raw_data_item_kind F.tot_parse_raw_data_item F.tot_serialize_raw_data_item;
    assert (Some? (LP.parse F.tot_parse_raw_data_item x));
    LP.parser_kind_prop_equiv F.parse_raw_data_item_kind F.tot_parse_raw_data_item;
    Some (y, n)

let parse_cbor_prefix x y =
  LP.parse_strong_prefix #F.parse_raw_data_item_kind F.tot_parse_raw_data_item x y

let serialize_parse_cbor x =
  assert (Some? (LP.parse F.tot_parse_raw_data_item (serialize_cbor x)))

let serialize_cbor_nonempty c =
  LP.tot_serialize_length F.tot_serialize_raw_data_item c

let deterministically_encoded_cbor_map_key_order = F.deterministically_encoded_cbor_map_key_order

let deterministically_encoded_cbor_map_key_order_irrefl x =
  Classical.move_requires (F.deterministically_encoded_cbor_map_key_order_irrefl x) x

let deterministically_encoded_cbor_map_key_order_trans x y z =
  F.deterministically_encoded_cbor_map_key_order_trans x y z

let deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 ext =
  let sq1 : squash (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m1) = () in
  let sq2 : squash (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m2) = () in
 F.deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 (fun k ->
  CBOR.Spec.Raw.EverParse.Assoc.list_ghost_assoc_eq k m1;
  CBOR.Spec.Raw.EverParse.Assoc.list_ghost_assoc_eq k m2;
  ext k) sq1 sq2

let list_sorted_map_entry_order_deterministically_encoded_cbor_map_key_order_no_repeats
  (#t: Type)
  (l: list (raw_data_item & t))
: Lemma
  (requires (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))
=   M.list_sorted_map_entry_order_no_repeats deterministically_encoded_cbor_map_key_order l

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
  (ensures (cbor_compare_array x1 x2 == LowParse.Spec.Sorted.lex_compare (F.tot_serialized_lex_compare F.tot_serialize_raw_data_item) x1 x2))
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
  (ensures (cbor_compare_map x1 x2 == LowParse.Spec.Sorted.lex_compare (F.tot_serialized_lex_compare (LowParse.Spec.Combinators.tot_serialize_nondep_then F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item)) x1 x2))
  (decreases x1)
= match x1, x2 with
  | a1 :: q1, a2 :: q2 ->
    cbor_compare_correct' (fst a1) (fst a2);
    cbor_compare_correct' (snd a1) (snd a2);
    F.tot_serialized_lex_compare_nondep_then F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item a1 a2;
    cbor_compare_map_correct q1 q2
  | _ -> ()

#pop-options

let cbor_compare_correct = cbor_compare_correct'

let serialize_cbor_tag tag =
  F.tot_serialize_header (F.raw_uint64_as_argument cbor_major_type_tagged tag)

let serialize_cbor_tag_length tag =
  LP.serialize_length F.serialize_header (F.raw_uint64_as_argument cbor_major_type_tagged tag)

#push-options "--z3rlimit 32"

let serialize_cbor_tag_correct tag payload =
  let v1 = Tagged tag payload in
  F.serialize_raw_data_item_aux_correct v1;
  LP.serialize_synth_eq
    _
    F.synth_raw_data_item
    (LP.serialize_dtuple2 F.serialize_header F.serialize_content)
    F.synth_raw_data_item_recip
    ()
    v1;
  let v1' = F.synth_raw_data_item_recip v1 in
  LP.serialize_dtuple2_eq F.serialize_header F.serialize_content v1'

#pop-options

module LPL = LowParse.Spec.VCList

let serialize_cbor_list l =
  LPL.tot_serialize_nlist (List.Tot.length l) F.tot_serialize_raw_data_item l

let serialize_cbor_list_nil () = ()

let serialize_cbor_list_cons a q =
  LPL.tot_serialize_nlist_cons (List.Tot.length q) F.tot_serialize_raw_data_item a q

#push-options "--z3rlimit 32"

let serialize_array_eq
  (len1: raw_uint64)
  (x1: list raw_data_item {List.Tot.length x1 == U64.v len1.value})
: Lemma
  (ensures (
    serialize_cbor (Array len1 x1) == F.serialize_header (F.raw_uint64_as_argument cbor_major_type_array len1) `Seq.append` serialize_cbor_list x1
  ))
= let v1 = Array len1 x1 in
  F.serialize_raw_data_item_aux_correct v1;
  LP.serialize_synth_eq
    _
    F.synth_raw_data_item
    (LP.serialize_dtuple2 F.serialize_header F.serialize_content)
    F.synth_raw_data_item_recip
    ()
    v1;
  let v1' = F.synth_raw_data_item_recip v1 in
  LP.serialize_dtuple2_eq F.serialize_header F.serialize_content v1';
  LowParse.Spec.VCList.tot_serialize_nlist_serialize_nlist (List.Tot.length x1) F.tot_serialize_raw_data_item x1

let serialize_cbor_array_length_gt_list len l =
  serialize_array_eq len l;
  LP.serialize_length F.serialize_header (F.raw_uint64_as_argument cbor_major_type_array len)

let serialize_string_eq
  (ty: major_type_byte_string_or_text_string)
  (len1: raw_uint64)
  (x1: Seq.lseq U8.t (U64.v len1.value) {
    ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct x1
  })
: Lemma
  (ensures (
    serialize_cbor (String ty len1 x1) == F.serialize_header (F.raw_uint64_as_argument ty len1) `Seq.append` x1
  ))
= let v1 = String ty len1 x1 in
  F.serialize_raw_data_item_aux_correct v1;
  LP.serialize_synth_eq
    _
    F.synth_raw_data_item
    (LP.serialize_dtuple2 F.serialize_header F.serialize_content)
    F.synth_raw_data_item_recip
    ()
    v1;
  let v1' = F.synth_raw_data_item_recip v1 in
  LP.serialize_dtuple2_eq F.serialize_header F.serialize_content v1';
  ()

let serialize_cbor_string_length_gt ty len l =
  serialize_string_eq ty len l;
  LP.serialize_length F.serialize_header (F.raw_uint64_as_argument ty len)

#pop-options

let serialize_cbor_map l =
  LPL.tot_serialize_nlist (List.Tot.length l) (LP.tot_serialize_nondep_then  F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item) l

let serialize_cbor_map_nil () = ()

#push-options "--z3rlimit 32"

let serialize_cbor_map_cons key value q =
  LPL.tot_serialize_nlist_cons (List.Tot.length q) (LP.tot_serialize_nondep_then  F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item) (key, value) q;
  LPL.tot_serialize_nondep_then_eq F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item (key, value);
  ()

#restart-solver

let rec serialize_cbor_map_insert_length'
  (m: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
  (ensures (match cbor_map_insert m kv with
  | None -> True
  | Some m' ->
    Seq.length (serialize_cbor_map m') == Seq.length (serialize_cbor_map m) + Seq.length (serialize_cbor (fst kv)) + Seq.length (serialize_cbor (snd kv))
  ))
  (decreases m)
= match m with
  | [] ->
    serialize_cbor_map_singleton (fst kv) (snd kv)
  | kv' :: q ->
    let c = cbor_map_entry_raw_compare kv' kv in
    if c < 0
    then begin
      match cbor_map_insert q kv with
      | Some q' ->
        assert (cbor_map_insert m kv == Some (kv' :: q'));
        serialize_cbor_map_cons (fst kv') (snd kv') q';
        serialize_cbor_map_insert_length' q kv;
        serialize_cbor_map_cons (fst kv') (snd kv') q;
        ()
      | _ -> ()
    end
    else if c > 0
    then begin
      assert (cbor_map_insert m kv == Some (kv :: m));
      serialize_cbor_map_cons (fst kv) (snd kv) m
    end
    else assert (cbor_map_insert m kv == None)

#pop-options

let serialize_cbor_map_insert_length m kv = serialize_cbor_map_insert_length' m kv

let parse_nlist_ext'
  (n: nat)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: (LP.parser k t))
  (#k': LP.parser_kind)
  (p' : LP.parser k' t)
  (sq: squash (forall x . LP.parse p x == LP.parse p' x))
  (b: LP.bytes)
: Lemma
  (ensures (LP.parse (LowParse.Spec.VCList.parse_nlist n p) b == LP.parse (LowParse.Spec.VCList.parse_nlist n p') b))
= LowParse.Spec.VCList.parse_nlist_ext n p p' b (fun x -> ())

#push-options "--z3rlimit 64 --split_queries always"

#restart-solver

let serialize_map_eq
  (len1: raw_uint64)
  (x1: list (raw_data_item & raw_data_item) {List.Tot.length x1 == U64.v len1.value})
: Lemma
  (ensures (
    serialize_cbor (Map len1 x1) == F.serialize_header (F.raw_uint64_as_argument cbor_major_type_map len1) `Seq.append` serialize_cbor_map x1
  ))
= let v1 = Map len1 x1 in
  F.serialize_raw_data_item_aux_correct v1;
  LP.serialize_synth_eq
    _
    F.synth_raw_data_item
    (LP.serialize_dtuple2 F.serialize_header F.serialize_content)
    F.synth_raw_data_item_recip
    ()
    v1;
  let v1' = F.synth_raw_data_item_recip v1 in
  LP.serialize_dtuple2_eq F.serialize_header F.serialize_content v1';
  assert (serialize_cbor (Map len1 x1) == F.serialize_header (F.raw_uint64_as_argument cbor_major_type_map len1) `Seq.append` F.serialize_content (dfst v1') (dsnd v1'));
  assert (F.serialize_content (dfst v1') (dsnd v1') == LowParse.Spec.VCList.serialize_nlist (List.Tot.length x1) #(LP.and_then_kind F.parse_raw_data_item_kind F.parse_raw_data_item_kind) #_ #(LP.nondep_then  F.parse_raw_data_item F.parse_raw_data_item) (LP.serialize_nondep_then  F.serialize_raw_data_item F.serialize_raw_data_item) x1);
  Classical.forall_intro (F.tot_nondep_then_eq_gen F.tot_parse_raw_data_item F.parse_raw_data_item F.tot_parse_raw_data_item F.parse_raw_data_item ());
  Classical.forall_intro (parse_nlist_ext' (List.Tot.length x1) #(LP.and_then_kind F.parse_raw_data_item_kind F.parse_raw_data_item_kind) (LP.tot_nondep_then  F.tot_parse_raw_data_item F.tot_parse_raw_data_item) (LP.nondep_then  F.parse_raw_data_item F.parse_raw_data_item) ());
  LP.serializer_unique_strong
    (LowParse.Spec.VCList.serialize_nlist (List.Tot.length x1) #(LP.and_then_kind F.parse_raw_data_item_kind F.parse_raw_data_item_kind) #_ #(LP.tot_nondep_then  F.tot_parse_raw_data_item F.tot_parse_raw_data_item) (LP.tot_serialize_nondep_then  F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item))
    (LowParse.Spec.VCList.serialize_nlist (List.Tot.length x1) (LP.serialize_nondep_then  F.serialize_raw_data_item F.serialize_raw_data_item))
    x1;
  assert (F.serialize_content (dfst v1') (dsnd v1') == LowParse.Spec.VCList.serialize_nlist (List.Tot.length x1) #(LP.and_then_kind F.parse_raw_data_item_kind F.parse_raw_data_item_kind) #_ #(LP.tot_nondep_then  F.tot_parse_raw_data_item F.tot_parse_raw_data_item) (LP.tot_serialize_nondep_then  F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item) x1);
  LowParse.Spec.VCList.tot_serialize_nlist_serialize_nlist (List.Tot.length x1) (LP.tot_serialize_nondep_then  F.tot_serialize_raw_data_item F.tot_serialize_raw_data_item) x1;
  ()

let cbor_serialize_map_length_gt_list
  len
  l
= serialize_map_eq len l;
  LP.serialize_length F.serialize_header (F.raw_uint64_as_argument cbor_major_type_map len)

#pop-options

let parse_cbor_map
  (n: nat)
  (s: Seq.seq U8.t)
: Pure (option (list (raw_data_item & raw_data_item) & nat))
    (requires True)
    (ensures fun res -> match res with
    | None -> True
    | Some (_, len) -> len <= Seq.length s
    )
= 
  match
    LPL.tot_parse_nlist n (LP.tot_nondep_then F.tot_parse_raw_data_item F.tot_parse_raw_data_item) s
  with
  | None -> None
  | Some (l, len) -> Some (l, len)

let parse_cbor_map_prefix
  (n: nat)
  (s1 s2: Seq.seq U8.t)
: Lemma
  (match parse_cbor_map n s1 with
  | None -> True
  | Some (l, len1) ->
    (len1 <= Seq.length s2 /\ Seq.slice s1 0 len1 == Seq.slice s2 0 len1) ==>
    parse_cbor_map n s2 == Some (l, len1)
  )
= match parse_cbor_map n s1 with
  | Some (l, len1) ->
    if len1 <= Seq.length s2 && Seq.slice s1 0 len1 = Seq.slice s2 0 len1
    then LP.parse_strong_prefix
      (LP.parser_of_tot_parser (LPL.tot_parse_nlist n (LP.tot_nondep_then F.tot_parse_raw_data_item F.tot_parse_raw_data_item)))
      s1 s2
  | _ -> ()

#push-options "--z3rlimit_factor 8"

let parse_cbor_map_equiv
  (n: nat)
  (s: Seq.seq U8.t)
  (l: list (raw_data_item & raw_data_item))
  (len: nat)
: Lemma
  (parse_cbor_map n s == Some (l, len) <==> (
    n == List.Tot.length l /\
    len <= Seq.length s /\
    Seq.slice s 0 len == serialize_cbor_map l
  ))
= if parse_cbor_map n s = Some (l, len)
  then LP.parse_injective
    (LP.parser_of_tot_parser (LPL.tot_parse_nlist n (LP.tot_nondep_then F.tot_parse_raw_data_item F.tot_parse_raw_data_item)))
    s (serialize_cbor_map l)
  else if n = List.Tot.length l && len <= Seq.length s && Seq.slice s 0 len = serialize_cbor_map l
  then parse_cbor_map_prefix n (serialize_cbor_map l) s
  else ()

#pop-options
