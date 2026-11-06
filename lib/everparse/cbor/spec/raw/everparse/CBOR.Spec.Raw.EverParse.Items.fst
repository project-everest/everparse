module CBOR.Spec.Raw.EverParse.Items
include CBOR.Spec.Raw.EverParse
open LowParse.Spec
open LowParse.Spec.Recursive
open LowParse.Spec.SeqBytes

(* Offset-based view of a byte sequence holding a list of consecutive
   CBOR raw data items, used to traverse an input buffer without
   splitting it. *)

module U64 = FStar.UInt64

let items_at (b: bytes) (o: nat) (n: nat) (l: list raw_data_item) : prop =
  o <= Seq.length b /\
  (match parse (parse_nlist n parse_raw_data_item) (Seq.slice b o (Seq.length b)) with
   | Some (l', _) -> (l' <: list raw_data_item) == l
   | None -> False)

let items_at_length (b: bytes) (o: nat) (n: nat) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures List.Tot.length l == n)
= ()

let slice_slice (b: bytes) (o: nat) (c: nat) : Lemma
  (requires o + c <= Seq.length b)
  (ensures Seq.slice (Seq.slice b o (Seq.length b)) c (Seq.length b - o) == Seq.slice b (o + c) (Seq.length b))
= Seq.slice_slice b o (Seq.length b) c (Seq.length b - o)

let items_at_hd (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures (
    match parse parse_raw_data_item (Seq.slice b o (Seq.length b)) with
    | Some (x, c) -> Cons? l /\ x == List.Tot.hd l /\ items_at b (o + c) (n - 1) (List.Tot.tl l)
    | None -> False
  ))
= let sb = Seq.slice b o (Seq.length b) in
  parse_nlist_eq n parse_raw_data_item sb;
  match parse parse_raw_data_item sb with
  | Some (_, c) -> slice_slice b o c
  | None -> ()

let items_at_intro_hd (b: bytes) (o: nat) (x: raw_data_item) (c: nat) (n: nat) (l: list raw_data_item) : Lemma
  (requires (
    o <= Seq.length b /\
    (match parse parse_raw_data_item (Seq.slice b o (Seq.length b)) with
     | Some (x', c') -> x' == x /\ (c' <: nat) == c
     | None -> False) /\
    items_at b (o + c) n l
  ))
  (ensures items_at b o (n + 1) (x :: l))
= let sb = Seq.slice b o (Seq.length b) in
  parse_nlist_eq (n + 1) parse_raw_data_item sb;
  slice_slice b o c

let items_at_single (b: bytes) (x: raw_data_item) (c: nat) : Lemma
  (requires (
    match parse parse_raw_data_item b with
    | Some (x', c') -> x' == x /\ (c' <: nat) == c
    | None -> False
  ))
  (ensures items_at b 0 1 [x] /\ items_at b c 0 [])
= Seq.slice_length b;
  parse_nlist_eq 0 parse_raw_data_item (Seq.slice b c (Seq.length b));
  items_at_intro_hd b 0 x c 0 []

(* Children of a raw data item, in serialization order *)

let children (a: raw_data_item) : Tot (list raw_data_item) =
  match a with
  | Array _ v -> v
  | Map _ v -> CBOR.Spec.Util.list_of_pair_list v
  | Tagged _ v -> [v]
  | _ -> []

let leaf_size (h: header) : Tot nat =
  let b = dfst h in
  if b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string
  then U64.v (argument_as_uint64 b (dsnd h))
  else 0

#push-options "--z3rlimit 32"

let synth_raw_data_item_from_alt_header_children
  (a: raw_data_item)
: Lemma
  (let (| lf, c |) = synth_raw_data_item_from_alt_recip a in
   dfst lf == get_raw_data_item_header a /\
   (c <: list raw_data_item) == children a /\
   (String? a ==> (LeafContentSeq? (dsnd lf) /\ (LeafContentSeq?.v (dsnd lf) <: bytes) == String?.v a))
  )
= ()

#pop-options

let parse_leaf_content_size (h: header) (b: bytes) : Lemma
  (ensures (
    match parse (parse_leaf_content h) b with
    | Some (lc, c) ->
      c == leaf_size h /\
      (LeafContentSeq? lc ==> (LeafContentSeq?.v lc <: bytes) == Seq.slice b 0 c)
    | None -> True
  ))
= let bh = dfst h in
  let long_arg = dsnd h in
  if bh.major_type = cbor_major_type_byte_string || bh.major_type = cbor_major_type_text_string
  then begin
    parse_filter_eq (parse_lseq_bytes (U64.v (argument_as_uint64 bh long_arg))) (lseq_utf8_correct (dfst h).major_type _) b;
    (parse_filter (parse_lseq_bytes (U64.v (argument_as_uint64 bh long_arg))) (lseq_utf8_correct (dfst h).major_type _) `parse_synth_eq` LeafContentSeq #h ()) b
  end
  else begin
    (parse_empty `parse_synth_eq` LeafContentEmpty #h ()) b
  end

#push-options "--z3rlimit 64"

let synth_recip_synth (y: raw_data_item_alt) : Lemma
  (synth_raw_data_item_from_alt_recip (synth_raw_data_item_from_alt y) == y)
= let x = synth_raw_data_item_from_alt y in
  let y' = synth_raw_data_item_from_alt_recip x in
  assert (synth_raw_data_item_from_alt y' == x);
  assert (synth_raw_data_item_from_alt y' == synth_raw_data_item_from_alt y)

let items_at_cons_aux (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures (
    Cons? l /\ (
    let a = List.Tot.hd l in
    let sb = Seq.slice b o (Seq.length b) in
    match parse parse_raw_data_item sb with
    | None -> False
    | Some (_, ca) ->
      match parse parse_leaf sb with
      | None -> False
      | Some (lf, c1) ->
        let sb1 = Seq.slice sb c1 (Seq.length sb) in
        match parse (parse_nlist (remaining_data_items lf) parse_raw_data_item) sb1 with
        | None -> False
        | Some (ch, c2) ->
          lf == dfst (synth_raw_data_item_from_alt_recip a) /\
          (ch <: list raw_data_item) == (dsnd (synth_raw_data_item_from_alt_recip a) <: list raw_data_item) /\
          (ca <: nat) == c1 + c2
  )))
= let sb = Seq.slice b o (Seq.length b) in
  items_at_hd b o n l;
  parse_recursive_eq' parse_raw_data_item_param sb;
  match parse tot_parse_leaf sb with
  | None -> ()
  | Some (lf, c1) ->
    let sb1 = Seq.slice sb c1 (Seq.length sb) in
    tot_parse_nlist_parse_nlist (remaining_data_items lf) tot_parse_raw_data_item sb1;
    match parse (tot_parse_nlist (remaining_data_items lf) tot_parse_raw_data_item) sb1 with
    | None -> ()
    | Some (ch, _) -> synth_recip_synth (| lf, ch |)

#pop-options

#push-options "--z3rlimit 64"

let items_at_cons (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures (
    Cons? l /\ (
    let a = List.Tot.hd l in
    let h = get_raw_data_item_header a in
    match parse parse_header (Seq.slice b o (Seq.length b)) with
    | None -> False
    | Some (h', c1) ->
      h' == h /\
      o + c1 + leaf_size h <= Seq.length b /\
      (String? a ==> Seq.slice b (o + c1) (o + c1 + leaf_size h) == String?.v a) /\
      items_at b (o + c1 + leaf_size h) (remaining_data_items_header h + (n - 1)) (children a `List.Tot.append` List.Tot.tl l)
  )))
= let sb = Seq.slice b o (Seq.length b) in
  items_at_hd b o n l;
  items_at_cons_aux b o n l;
  let a = List.Tot.hd l in
  synth_raw_data_item_from_alt_header_children a;
  let Some (_, ca) = parse parse_raw_data_item sb in
  let Some (lf, cl) = parse parse_leaf sb in
  parse_dtuple2_eq parse_header parse_leaf_content sb;
  let Some (h, c1) = parse parse_header sb in
  let sb1 = Seq.slice sb c1 (Seq.length sb) in
  parse_leaf_content_size h sb1;
  let Some (lc, c2) = parse (parse_leaf_content h) sb1 in
  assert (cl == c1 + c2);
  slice_slice b o cl;
  slice_slice b o c1;
  let o' = o + cl in
  let sb' = Seq.slice b o' (Seq.length b) in
  let k = remaining_data_items_header h in
  parse_nlist_sum parse_raw_data_item k (n - 1) sb';
  slice_slice b o ca;
  assert (Seq.slice sb' (ca - cl) (Seq.length sb') == Seq.slice b (o + ca) (Seq.length b));
  if String? a
  then begin
    assert (Seq.slice b (o + c1) (o + c1 + c2) `Seq.equal` Seq.slice sb1 0 c2)
  end

#pop-options

#push-options "--z3rlimit 64"

(* The size of an item is the size of its header and leaf content plus
   the size of its children *)

let items_at_cons_size (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures (
    match parse parse_raw_data_item (Seq.slice b o (Seq.length b)) with
    | None -> False
    | Some (_, ca) ->
      match parse parse_header (Seq.slice b o (Seq.length b)) with
      | None -> False
      | Some (h, c1) ->
        o + c1 + leaf_size h <= Seq.length b /\
        (match parse (parse_nlist (remaining_data_items_header h) parse_raw_data_item) (Seq.slice b (o + c1 + leaf_size h) (Seq.length b)) with
         | None -> False
         | Some (_, c3) -> (ca <: nat) == c1 + leaf_size h + c3)
  ))
= let sb = Seq.slice b o (Seq.length b) in
  items_at_hd b o n l;
  items_at_cons_aux b o n l;
  items_at_cons b o n l;
  let Some (_, ca) = parse parse_raw_data_item sb in
  let Some (lf, cl) = parse parse_leaf sb in
  parse_dtuple2_eq parse_header parse_leaf_content sb;
  let Some (h, c1) = parse parse_header sb in
  let sb1 = Seq.slice sb c1 (Seq.length sb) in
  parse_leaf_content_size h sb1;
  let Some (lc, c2) = parse (parse_leaf_content h) sb1 in
  assert (cl == c1 + c2);
  slice_slice b o cl;
  assert (remaining_data_items lf == remaining_data_items_header h)

#pop-options
