module LowParse.Spec.RecursiveVLGen

open LowParse.Spec.Combinators
open LowParse.Spec.RecursiveGen
open LowParse.Spec.List
open LowParse.Spec.BoundedInt

module Seq = FStar.Seq
module U32 = FStar.UInt32
module VL = LowParse.Tot.VLGen

let rec tot_parse_list_ext
  (#k: parser_kind)
  (#t: Type)
  (p1 p2: tot_parser k t)
  (b: bytes)
: Lemma
  (requires (parse_rec_gen_ih_agree p1 p2 b))
  (ensures (parse (tot_parse_list p1) b == parse (tot_parse_list p2) b))
  (decreases (Seq.length b))
= tot_parse_list_eq p1 b;
  tot_parse_list_eq p2 b;
  if Seq.length b = 0
  then ()
  else match parse p1 b with
  | None -> ()
  | Some (_, n) ->
    if n = 0
    then ()
    else tot_parse_list_ext p1 p2 (Seq.slice b n (Seq.length b))

let rec_vlgen_body_ext
  (p: rec_vlgen_param)
  (ih1 ih2: tot_parser (rec_vlgen_kind p) p.t)
  (h: p.tag)
  (b: bytes)
: Lemma
  (requires (parse_rec_gen_ih_agree ih1 ih2 b))
  (ensures (parse (rec_vlgen_body p ih1 h) b == parse (rec_vlgen_body p ih2 h) b))
= if p.is_node h
  then begin
    tot_parse_synth_eq (tot_parse_list ih1) (RNode #p.t #(p.leaf_t h)) b;
    tot_parse_synth_eq (tot_parse_list ih2) (RNode #p.t #(p.leaf_t h)) b;
    tot_parse_list_ext ih1 ih2 b
  end
  else ()

let rec_vlgen_payload_parser_eq
  (p: rec_vlgen_param)
  (ih: tot_parser (rec_vlgen_kind p) p.t)
  (h: p.tag)
  (b: bytes)
: Lemma
  (parse (rec_vlgen_payload_parser p ih h) b == begin match parse p.parse_len b with
  | None -> None
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then None
    else match parse (rec_vlgen_body p ih h) (Seq.slice b sz (sz + U32.v len)) with
    | Some (x, consumed_x) ->
      if consumed_x = U32.v len
      then Some (x, sz + U32.v len)
      else None
    | _ -> None
  end)
= ()

let rec_vlgen_payload_ext
  p ih1 ih2 h b
= rec_vlgen_payload_parser_eq p ih1 h b;
  rec_vlgen_payload_parser_eq p ih2 h b;
  match parse p.parse_len b with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then ()
    else rec_vlgen_body_ext p ih1 ih2 h (Seq.slice b sz (sz + U32.v len))

let parse_rec_vlgen_eq
  p b
= let q = rec_vlgen_gen_param p in
  parse_rec_gen_eq' q b;
  match parse p.parse_tag b with
  | None -> ()
  | Some (h, c1) ->
    let b2 = Seq.slice b c1 (Seq.length b) in
    rec_vlgen_payload_parser_eq p (parse_rec_vlgen p) h b2;
    match parse p.parse_len b2 with
    | None -> ()
    | Some (len, c2) ->
      if Seq.length b2 < c2 + U32.v len
      then ()
      else Seq.slice_slice b c1 (Seq.length b) c2 (c2 + U32.v len)

let strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (x: bytes)
  (m: nat { m <= Seq.length x })
: Lemma
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (parse p (Seq.slice x 0 m) == begin match parse p x with
  | Some (v, c) -> if c <= m then Some (v, c) else None
  | None -> None
  end))
= let w = Seq.slice x 0 m in
  match parse p x with
  | Some (_, c) ->
    if c <= m
    then parse_strong_prefix #k p x w
    else begin match parse p w with
    | None -> ()
    | Some _ -> parse_strong_prefix #k p w x
    end
  | None ->
    begin match parse p w with
    | None -> ()
    | Some _ -> parse_strong_prefix #k p w x
    end

let rec_vlgen_header_prefix
  (p: rec_vlgen_param)
  (x: bytes)
  (m: nat { m <= Seq.length x })
: Lemma
  (rec_vlgen_header p (Seq.slice x 0 m) == begin match rec_vlgen_header p x with
  | Some (h, hs, len) -> if hs <= m then Some (h, hs, len) else None
  | None -> None
  end)
= let w = Seq.slice x 0 m in
  strong_prefix p.parse_tag x m;
  match parse p.parse_tag x with
  | None -> ()
  | Some (h, c1) ->
    if c1 <= m
    then begin
      let x2 = Seq.slice x c1 (Seq.length x) in
      let w2 = Seq.slice w c1 (Seq.length w) in
      Seq.slice_slice x 0 m c1 m;
      Seq.slice_slice x c1 (Seq.length x) 0 (m - c1);
      assert (w2 `Seq.equal` Seq.slice x2 0 (m - c1));
      strong_prefix p.parse_len x2 (m - c1)
    end
    else ()

let rec_vlgen_hdr_prefix
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: Lemma
  (rec_vlgen_header p (Seq.slice v i e) == begin match rec_vlgen_hdr p v i with
  | Some (h, hs, len) -> if i + hs <= e then Some (h, hs, len) else None
  | None -> None
  end)
= Seq.slice_slice v i (Seq.length v) 0 (e - i);
  assert (Seq.slice v i e `Seq.equal` Seq.slice (Seq.slice v i (Seq.length v)) 0 (e - i));
  rec_vlgen_header_prefix p (Seq.slice v i (Seq.length v)) (e - i)

let rec_vlgen_hdr_pos
  p v i
= let x = Seq.slice v i (Seq.length v) in
  parser_kind_prop_equiv p.tag_kind p.parse_tag;
  parser_kind_prop_equiv p.len_kind p.parse_len;
  match parse p.parse_tag x with
  | None -> ()
  | Some (_, c1) -> ()

let rec_vlgen_list_ok_nil
  p v i
= tot_parse_list_eq (parse_rec_vlgen p) (Seq.slice v i i)

let rec_vlgen_body_ok
  (p: rec_vlgen_param)
  (h: p.tag)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: Lemma
  (begin match parse (rec_vlgen_body p (parse_rec_vlgen p) h) (Seq.slice v i e) with
  | Some (_, c) -> c = e - i
  | None -> false
  end == rec_vlgen_elem_ok p h v i e)
= let w = Seq.slice v i e in
  if p.is_node h
  then begin
    tot_parse_synth_eq (tot_parse_list (parse_rec_vlgen p)) (RNode #p.t #(p.leaf_t h)) w;
    parser_kind_prop_equiv (parse_list_kind (rec_vlgen_kind p).parser_kind_injective) (tot_parse_list (parse_rec_vlgen p))
  end
  else begin
    tot_parse_synth_eq (p.leaf h) (RLeaf #p.t #(p.leaf_t h)) w
  end

#push-options "--z3rlimit 32"

#restart-solver
let rec_vlgen_list_ok_cons
  p v i e
= let w = Seq.slice v i e in
  let r = parse_rec_vlgen p in
  tot_parse_list_eq r w;
  parse_rec_vlgen_eq p w;
  rec_vlgen_hdr_prefix p v i e;
  rec_vlgen_hdr_pos p v i;
  match rec_vlgen_hdr p v i with
  | None -> ()
  | Some (h, hs, len) ->
    if i + hs + len > e
    then ()
    else begin
      Seq.slice_slice v i e hs (hs + len);
      Seq.slice_slice v i e (hs + len) (e - i);
      rec_vlgen_body_ok p h v (i + hs) (i + hs + len)
    end

#pop-options

let rec rec_vlgen_list_ok_tiles_aux
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: Lemma
  (requires (rec_vlgen_list_ok p v i e))
  (ensures (rec_vlgen_tiles p v i e))
  (decreases (e - i))
= if i = e
  then ()
  else begin
    rec_vlgen_list_ok_cons p v i e;
    rec_vlgen_hdr_pos p v i;
    let Some (_, hs, len) = rec_vlgen_hdr p v i in
    rec_vlgen_list_ok_tiles_aux p v (i + hs + len) e
  end

let rec_vlgen_list_ok_tiles p v i e = rec_vlgen_list_ok_tiles_aux p v i e

let rec rec_vlgen_list_ok_split_aux
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (m: nat)
  (e: nat { i <= m /\ m <= e /\ e <= Seq.length v })
: Lemma
  (requires (rec_vlgen_tiles p v i m))
  (ensures (rec_vlgen_list_ok p v i e == (rec_vlgen_list_ok p v i m && rec_vlgen_list_ok p v m e)))
  (decreases (m - i))
= if i = m
  then rec_vlgen_list_ok_nil p v i
  else begin
    rec_vlgen_list_ok_cons p v i e;
    rec_vlgen_list_ok_cons p v i m;
    rec_vlgen_hdr_pos p v i;
    let Some (_, hs, len) = rec_vlgen_hdr p v i in
    rec_vlgen_list_ok_split_aux p v (i + hs + len) m e
  end

let rec_vlgen_list_ok_split p v i m e = rec_vlgen_list_ok_split_aux p v i m e

#push-options "--z3rlimit 32"

#restart-solver
let parse_rec_vlgen_ok
  p v i
= let x = Seq.slice v i (Seq.length v) in
  parse_rec_vlgen_eq p x;
  rec_vlgen_hdr_pos p v i;
  match rec_vlgen_hdr p v i with
  | None -> ()
  | Some (h, hs, len) ->
    if i + hs + len > Seq.length v
    then ()
    else begin
      Seq.slice_slice v i (Seq.length v) hs (hs + len);
      rec_vlgen_body_ok p h v (i + hs) (i + hs + len)
    end

#pop-options
