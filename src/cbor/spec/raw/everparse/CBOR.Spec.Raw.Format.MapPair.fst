module CBOR.Spec.Raw.Format.MapPair
friend CBOR.Spec.API.Type
friend CBOR.Spec.Raw.DataModel
open LowParse.Spec.Combinators
open LowParse.Spec.VCList
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open CBOR.Spec.Util
open LowParse.Spec.SeqBytes

module RF = CBOR.Spec.Raw.Format
module R = CBOR.Spec.Raw.Sort

let cbor_map_bool (x: list (R.raw_data_item & R.raw_data_item)) : Tot bool =
  List.Tot.for_all (holds_on_pair R.raw_data_item_ints_optimal) x &&
  List.Tot.for_all (holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order)) x &&
  List.Tot.sorted (R.map_entry_order RF.deterministically_encoded_cbor_map_key_order _) x

let synth_cbor_map
  (x: parse_filter_refine (cbor_map_bool))
: Tot cbor_map
= x

let synth_cbor_map_recip
  (x: cbor_map)
: Tot (parse_filter_refine (cbor_map_bool))
= x

let tot_parse_cbor_map : tot_parser _ cbor_map =
  tot_parse_synth
    (tot_parse_filter
      (tot_parse_list (tot_nondep_then tot_parse_raw_data_item tot_parse_raw_data_item))
      cbor_map_bool
    )
    synth_cbor_map

let rec tot_parse_list_parse_list
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (b: bytes)
: Lemma
  (ensures (parse (tot_parse_list p) b == parse (parse_list (parser_of_tot_parser p)) b))
  (decreases (Seq.length b))
= tot_parse_list_eq p b;
  parse_list_eq (parser_of_tot_parser p) b;
  if Seq.length b = 0
  then ()
  else match parse p b with
  | None -> ()
  | Some (v, n) ->
    if n = 0
    then ()
    else tot_parse_list_parse_list p (Seq.slice b n (Seq.length b))

let rec tot_serialize_list'
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (x: list t)
: Tot bytes
= match x with
  | [] -> Seq.empty
  | a :: q -> Seq.append (s a) (tot_serialize_list' s q)

let rec tot_serialize_list'_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
  (x: list t)
: Lemma
  (ensures (tot_serialize_list' s x == bare_serialize_list (parser_of_tot_parser p) (serializer_of_tot_serializer s) x))
  (decreases x)
= match x with
  | [] -> ()
  | _ :: q -> tot_serialize_list'_eq s q

let tot_serialize_list
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer p)
: Pure (tot_serializer (tot_parse_list p))
  (requires (
    serialize_list_precond k
  ))
  (ensures (fun _ -> True))
= Classical.forall_intro (tot_parse_list_parse_list p);
  Classical.forall_intro (tot_serialize_list'_eq s);
  bare_serialize_list_correct (parser_of_tot_parser p) (serializer_of_tot_serializer s);
  tot_serialize_list' s

let tot_serialize_cbor_map : tot_serializer tot_parse_cbor_map =
  tot_serialize_synth
    _
    synth_cbor_map
    (tot_serialize_filter
      (tot_serialize_list (tot_serialize_nondep_then tot_serialize_raw_data_item tot_serialize_raw_data_item))
      cbor_map_bool
    )
    synth_cbor_map_recip
    ()

let cbor_map_order (x1 x2: cbor_map) : Tot bool =
  bytes_lex_order (tot_serialize_cbor_map x1) (tot_serialize_cbor_map x2)

let cbor_map_order_irrefl' (x: cbor_map) : Lemma
  (requires (cbor_map_order x x))
  (ensures False)
= bytes_lex_order_irrefl (tot_serialize_cbor_map x) (tot_serialize_cbor_map x)

let cbor_map_order_irrefl : squash (order_irrefl cbor_map_order) =
  Classical.forall_intro (Classical.move_requires cbor_map_order_irrefl')

let cbor_map_order_trans' (x y z: cbor_map) : Lemma
  ((cbor_map_order x y /\ cbor_map_order y z) ==> cbor_map_order x z)
= Classical.move_requires (bytes_lex_order_trans (tot_serialize_cbor_map x) (tot_serialize_cbor_map y)) (tot_serialize_cbor_map z)

let cbor_map_order_trans : squash (order_trans cbor_map_order) =
  Classical.forall_intro_3 cbor_map_order_trans'

let cbor_map_order_total'
  (x y: cbor_map)
: Lemma
  (x == y \/ cbor_map_order x y \/ cbor_map_order y x)
= bytes_lex_order_total (tot_serialize_cbor_map x) (tot_serialize_cbor_map y)

let cbor_map_order_total : squash (forall x y . x == y \/ cbor_map_order x y \/ cbor_map_order y x) =
  Classical.forall_intro_2 cbor_map_order_total'

let map_pair_order
  (x1 x2: (cbor_map & cbor_map))
: Tot bool
= cbor_map_order (fst x1) (fst x2) ||
  (fst x1 = fst x2 && cbor_map_order (snd x1) (snd x2))

let map_pair_order_irrefl = ()

let map_pair_order_trans = ()

let map_pair_order_total = ()
