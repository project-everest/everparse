module LowParse.Spec.RecursiveVLGen
include LowParse.Spec.RecursiveGen
include LowParse.Spec.List
include LowParse.Spec.BoundedInt

(* Length-delimited recursive parser: a value is a tag, then a length,
   then exactly that many bytes of content. Depending on the tag, the
   content is either a list of recursive values ("node") or a leaf.
   This is an instance of LowParse.Spec.RecursiveGen. A typical instance
   is the generic ASN.1 DER TLV tree.

   This module also gives position-based characterizations (`rec_vlgen_list_ok`,
   `rec_vlgen_tiles`) used by the constant-stack validator in
   LowParse.Pulse.RecursiveVLGen. *)

module Seq = FStar.Seq
module U32 = FStar.UInt32
module VL = LowParse.Tot.VLGen

type rec_vlgen_payload (t: Type) (leaf: Type) =
| RNode: (children: list t) -> rec_vlgen_payload t leaf
| RLeaf: (v: leaf) -> rec_vlgen_payload t leaf

let rec_vlgen_body_kind (inj: bool) : Tot parser_kind = {
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = None;
  parser_kind_metadata = None;
  parser_kind_injective = inj;
}

let rec_vlgen_payload_kind (inj: bool) : Tot parser_kind = {
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
  parser_kind_injective = inj;
}

[@@(noextract_to "krml")]
inline_for_extraction
noeq
type rec_vlgen_param = {
  t: Type;
  tag: Type;
  tag_kind: parse_rec_gen_header_kind;
  parse_tag: tot_parser tag_kind tag;
  len_min: nat;
  len_max: (n: nat { len_min <= n /\ n < 4294967296 });
  len_kind: (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ (tag_kind.parser_kind_injective ==> k.parser_kind_injective) });
  parse_len: tot_parser len_kind (bounded_int32 len_min len_max);
  is_node: (tag -> bool);
  leaf_t: (tag -> Type);
  leaf_kind: (k: parser_kind { tag_kind.parser_kind_injective ==> k.parser_kind_injective });
  leaf: ((h: tag) -> tot_parser leaf_kind (leaf_t h));
  synth_: (dtuple2 tag (fun h -> rec_vlgen_payload t (leaf_t h)) -> t);
  synth_inj: squash (synth_injective synth_);
}

let rec_vlgen_kind (p: rec_vlgen_param) : Tot parser_kind = parse_rec_gen_kind p.tag_kind

let rec_vlgen_body
  (p: rec_vlgen_param)
  (ih: tot_parser (rec_vlgen_kind p) p.t)
  (h: p.tag)
: Tot (tot_parser (rec_vlgen_body_kind p.tag_kind.parser_kind_injective) (rec_vlgen_payload p.t (p.leaf_t h)))
= if p.is_node h
  then tot_weaken _ (tot_parse_synth (tot_parse_list ih) (RNode #p.t #(p.leaf_t h)))
  else tot_weaken _ (tot_parse_synth (p.leaf h) (RLeaf #p.t #(p.leaf_t h)))

let rec_vlgen_payload_parser
  (p: rec_vlgen_param)
  (ih: tot_parser (rec_vlgen_kind p) p.t)
  (h: p.tag)
: Tot (tot_parser (rec_vlgen_payload_kind p.tag_kind.parser_kind_injective) (rec_vlgen_payload p.t (p.leaf_t h)))
= tot_weaken _ (VL.parse_vlgen_weak p.len_min p.len_max p.parse_len (rec_vlgen_body p ih h))

val rec_vlgen_payload_ext
  (p: rec_vlgen_param)
  (ih1 ih2: tot_parser (rec_vlgen_kind p) p.t)
  (h: p.tag)
  (b: bytes)
: Lemma
  (requires (parse_rec_gen_ih_agree ih1 ih2 b))
  (ensures (parse (rec_vlgen_payload_parser p ih1 h) b == parse (rec_vlgen_payload_parser p ih2 h) b))

let rec_vlgen_gen_param
  (p: rec_vlgen_param)
: Tot parse_rec_gen_param
= {
    t = p.t;
    header = p.tag;
    header_kind = p.tag_kind;
    parse_header = p.parse_tag;
    payload_t = (fun h -> rec_vlgen_payload p.t (p.leaf_t h));
    payload_kind = rec_vlgen_payload_kind p.tag_kind.parser_kind_injective;
    payload = rec_vlgen_payload_parser p;
    payload_ext = rec_vlgen_payload_ext p;
    synth_ = p.synth_;
    synth_inj = p.synth_inj;
  }

let parse_rec_vlgen
  (p: rec_vlgen_param)
: Tot (tot_parser (rec_vlgen_kind p) p.t)
= parse_rec_gen (rec_vlgen_gen_param p)

(* Header: tag and length. Returns the tag, the header size and the content length. *)

let rec_vlgen_header
  (p: rec_vlgen_param)
  (b: bytes)
: GTot (option (p.tag & nat & nat))
= match parse p.parse_tag b with
  | None -> None
  | Some (h, c1) ->
    begin match parse p.parse_len (Seq.slice b c1 (Seq.length b)) with
    | None -> None
    | Some (len, c2) -> Some (h, c1 + c2, U32.v len)
    end

val parse_rec_vlgen_eq
  (p: rec_vlgen_param)
  (b: bytes)
: Lemma
  (parse (parse_rec_vlgen p) b == begin match rec_vlgen_header p b with
  | None -> None
  | Some (h, hs, len) ->
    if hs + len > Seq.length b
    then None
    else match parse (rec_vlgen_body p (parse_rec_vlgen p) h) (Seq.slice b hs (hs + len)) with
    | None -> None
    | Some (pl, c) ->
      if c = len
      then Some (p.synth_ (| h, pl |), hs + len)
      else None
  end)

(* Position-based characterizations, on a fixed input `v` *)

let rec_vlgen_hdr
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat { i <= Seq.length v })
: GTot (option (p.tag & nat & nat))
= rec_vlgen_header p (Seq.slice v i (Seq.length v))

val rec_vlgen_hdr_pos
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat { i <= Seq.length v })
: Lemma
  (match rec_vlgen_hdr p v i with
  | Some (_, hs, _) -> hs > 0 /\ i + hs <= Seq.length v
  | None -> True)

let rec_vlgen_list_ok
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: GTot bool
= Some? (parse (tot_parse_list (parse_rec_vlgen p)) (Seq.slice v i e))

let rec_vlgen_leaf_ok
  (p: rec_vlgen_param)
  (h: p.tag)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: GTot bool
= match parse (p.leaf h) (Seq.slice v i e) with
  | Some (_, c) -> c = e - i
  | None -> false

let rec_vlgen_elem_ok
  (p: rec_vlgen_param)
  (h: p.tag)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: GTot bool
= if p.is_node h
  then rec_vlgen_list_ok p v i e
  else rec_vlgen_leaf_ok p h v i e

(* Whether the headers of the direct children of a node exactly tile [i, e) *)
let rec rec_vlgen_tiles
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: GTot bool
  (decreases (e - i))
= if i = e
  then true
  else match rec_vlgen_hdr p v i with
  | None -> false
  | Some (_, hs, len) ->
    if hs = 0 || i + hs + len > e
    then false
    else rec_vlgen_tiles p v (i + hs + len) e

val rec_vlgen_list_ok_nil
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat { i <= Seq.length v })
: Lemma
  (rec_vlgen_list_ok p v i i == true)

val rec_vlgen_list_ok_cons
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i < e /\ e <= Seq.length v })
: Lemma
  (rec_vlgen_list_ok p v i e == begin match rec_vlgen_hdr p v i with
  | None -> false
  | Some (h, hs, len) ->
    i + hs + len <= e &&
    rec_vlgen_elem_ok p h v (i + hs) (i + hs + len) &&
    rec_vlgen_list_ok p v (i + hs + len) e
  end)

val rec_vlgen_list_ok_tiles
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: Lemma
  (requires (rec_vlgen_list_ok p v i e))
  (ensures (rec_vlgen_tiles p v i e))

val rec_vlgen_list_ok_split
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (m: nat)
  (e: nat { i <= m /\ m <= e /\ e <= Seq.length v })
: Lemma
  (requires (rec_vlgen_tiles p v i m))
  (ensures (rec_vlgen_list_ok p v i e == (rec_vlgen_list_ok p v i m && rec_vlgen_list_ok p v m e)))

val parse_rec_vlgen_ok
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat { i <= Seq.length v })
: Lemma
  (match parse (parse_rec_vlgen p) (Seq.slice v i (Seq.length v)) with
  | Some (_, c) ->
    begin match rec_vlgen_hdr p v i with
    | Some (h, hs, len) ->
      c == hs + len /\ i + hs + len <= Seq.length v /\ rec_vlgen_elem_ok p h v (i + hs) (i + hs + len)
    | None -> False
    end
  | None ->
    begin match rec_vlgen_hdr p v i with
    | Some (h, hs, len) ->
      i + hs + len <= Seq.length v ==> rec_vlgen_elem_ok p h v (i + hs) (i + hs + len) == false
    | None -> True
    end
  )
