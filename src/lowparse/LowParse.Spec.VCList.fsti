(* Variable-count lists *)

module LowParse.Spec.VCList
include LowParse.Spec.Combinators // for seq_slice_append_l
include LowParse.Spec.Array // for vlarray

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot

inline_for_extraction
type nlist (n: nat) (t: Type) = (l: list t { L.length l == n } )

// abstract
inline_for_extraction
let nlist_nil (#t: Type) : Tot (nlist 0 t) = []

// abstract
let nlist_nil_unique (t: Type) (l: nlist 0 t) : Lemma (l == nlist_nil) = ()

// abstract
inline_for_extraction
let nlist_cons (#t: Type) (#n: nat) (a: t) (q: nlist n t) : Tot (nlist (n + 1) t) =
  a :: q

// abstract
inline_for_extraction
let nlist_destruct (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Tot (t * nlist n t) =
  match x with (a :: q) -> a, q

// abstract
let nlist_cons_unique (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Lemma
  (let (a, q) = nlist_destruct x in x == nlist_cons a q)
= ()

unfold let mul = Prims.op_Multiply

inline_for_extraction
let synth_nlist (#t: Type) (n: nat) (xy: t * nlist n t) : Tot (nlist (n + 1) t) =
  match xy with (x, y) ->
  nlist_cons x y

inline_for_extraction
let synth_nlist_recip (#t: Type) (n: nat) (xy: nlist (n + 1) t) : Tot (t * nlist n t) =
  nlist_destruct xy

// abstract
let synth_inverse_1 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist #t n) (synth_nlist_recip n))
= ()

// abstract
let synth_inverse_2 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist_recip #t n) (synth_nlist n))
= ()

let rec parse_nlist_kind'
  (n: nat)
  (k: parser_kind)
: GTot parser_kind
  (decreases n)
= if n = 0
  then parse_ret_kind
  else k `and_then_kind` parse_nlist_kind' (n - 1) k

let rec parse_nlist_kind_low
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_low == n `mul` k.parser_kind_low)
= if n = 0
  then ()
  else begin
    LowParse.Math.distributivity_add_left (n - 1) 1 k.parser_kind_low;
    parse_nlist_kind_low (n - 1) k
  end

let rec parse_nlist_kind_high
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_high == (match k.parser_kind_high with
    | None -> if n = 0 then Some 0 else None
    | Some b -> Some (n `mul` b)
  ))
= if n = 0
  then ()
  else begin
    begin match k.parser_kind_high with
    | None -> ()
    | Some b -> LowParse.Math.distributivity_add_left (n - 1) 1 b
    end;
    parse_nlist_kind_high (n - 1) k
  end

let rec parse_nlist_kind_metadata
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_metadata == (if n = 0 then Some ParserKindMetadataTotal else k.parser_kind_metadata))
= if n = 0
  then ()
  else parse_nlist_kind_metadata (n - 1) k

let rec parse_nlist_kind_subkind
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_subkind == (
    if n = 0 then Some ParserStrong else k.parser_kind_subkind
  ))
= if n = 0
  then ()
  else parse_nlist_kind_subkind (n - 1) k

inline_for_extraction
let parse_nlist_kind
  (n: nat)
  (k: parser_kind)
: Tot (k' : parser_kind { k' == parse_nlist_kind' n k })
= [@inline_let] let _ =
    parse_nlist_kind_low n k;
    parse_nlist_kind_high n k;
    parse_nlist_kind_metadata n k;
    parse_nlist_kind_subkind n k
  in
  {
    parser_kind_low = n `mul` k.parser_kind_low;
    parser_kind_high = (match k.parser_kind_high with
    | None -> if n = 0 then Some 0 else None
    | Some b -> Some (n `mul` b)
    );
    parser_kind_metadata = (if n = 0 then Some ParserKindMetadataTotal else k.parser_kind_metadata);
    parser_kind_subkind = (if n = 0 then Some ParserStrong else k.parser_kind_subkind);
  }

let rec parse_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_nlist_kind n k) (nlist n t))
= if n = 0
  then parse_ret nlist_nil
  else begin
    [@inline_let] let _ = assert (parse_nlist_kind n k == parse_nlist_kind' n k) in
    parse_synth
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
  end

val parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (y: parser (parse_nlist_kind n k) (nlist n t) { y == parse_nlist' n p } )

let parse_nlist_eq
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist n p) b == (
    if n = 0
    then Some ([], 0)
    else match parse p b with
    | Some (elem, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      begin match parse (parse_nlist (n - 1) p) b' with
      | Some (q, consumed') -> Some (elem :: q, consumed + consumed')
      | _ -> None
      end
    | _ -> None
  ))
= if n = 0
  then ()
  else begin
    parse_synth_eq
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
      b;
    nondep_then_eq p (parse_nlist' (n - 1) p) b
  end

let rec serialize_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (serializer (parse_nlist n p))
= if n = 0
  then begin
    Classical.forall_intro (nlist_nil_unique t);
    (fun _ -> Seq.empty)
  end
  else begin
    synth_inverse_1 t (n - 1);
    synth_inverse_2 t (n - 1);
    serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then s (serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()
  end

val serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (y: serializer (parse_nlist n p) { y == serialize_nlist' n s })

let serialize_nlist_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Lemma
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.empty))
= ()

let serialize_nlist_cons
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (a: t)
  (q: nlist n t)
: Lemma
  (ensures (
    serialize (serialize_nlist (n + 1) s) (a :: q) == Seq.append (serialize s a) (serialize (serialize_nlist n s) q)
  ))
= serialize_synth_eq _ (synth_nlist n) (serialize_nondep_then s (serialize_nlist' n s)) (synth_nlist_recip n) () (a :: q);
  serialize_nondep_then_eq s (serialize_nlist' n s) (a, q)

(* variable-count lists proper *)

let bounded_count_prop
  (min max: nat)
  (x: U32.t)
: GTot bool
= min <= U32.v x && U32.v x <= max

inline_for_extraction
let bounded_count (min max: nat) : Tot Type = (x: U32.t { bounded_count_prop min max x == true } )

inline_for_extraction
let parse_vclist_payload_kind
  (min: nat)
  (max: nat { min <= max } )
  (k: parser_kind)
: Tot parser_kind
= {
    parser_kind_low = min `mul` k.parser_kind_low;
    parser_kind_high = (match k.parser_kind_high with
    | None -> if max = 0 then Some 0 else None
    | Some b -> Some (max `mul` b)
    );
    parser_kind_metadata = (if max = 0 then Some ParserKindMetadataTotal else if min = 0 && k.parser_kind_metadata <> Some ParserKindMetadataTotal then None else k.parser_kind_metadata);
    parser_kind_subkind = (if max = 0 then Some ParserStrong else if min = 0 && k.parser_kind_subkind <> Some ParserStrong then None else k.parser_kind_subkind);
  }

let parse_vclist_payload_kind_is_weaker_than
  (min: nat)
  (max: nat)
  (n: nat { min <= n /\ n <= max })
  (k: parser_kind)
: Lemma
  (parse_vclist_payload_kind min max k `is_weaker_than` parse_nlist_kind n k)
  [SMTPat (parse_vclist_payload_kind min max k `is_weaker_than` parse_nlist_kind n k)]
= FStar.Math.Lemmas.lemma_mult_le_right k.parser_kind_low min n;
  match k.parser_kind_high with
  | None -> ()
  | Some high -> FStar.Math.Lemmas.lemma_mult_le_right high n max

inline_for_extraction
let synth_vclist_payload
  (min: nat)
  (max: nat)
  (n: bounded_count min max)
  (#t: Type)
  (x: nlist (U32.v n) t)
: Tot (vlarray t min max)
= x

let parse_vclist_payload
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: bounded_count min max)
: Tot (parser (parse_vclist_payload_kind min max k) (vlarray t min max))
= weaken (parse_vclist_payload_kind min max k) (parse_synth (parse_nlist (U32.v n) p) (synth_vclist_payload min max n))

inline_for_extraction
let parse_vclist_kind
  (min: nat)
  (max: nat { min <= max } )
  (lk: parser_kind)
  (k: parser_kind)
: Tot parser_kind
= parse_filter_kind lk `and_then_kind` parse_vclist_payload_kind min max k

inline_for_extraction
let synth_bounded_count
  (min: nat)
  (max: nat { min <= max } )
  (x: U32.t { bounded_count_prop min max x == true } )
: Tot (bounded_count min max)
= x

let parse_vclist_and_then_cases_injective
  (min: nat)
  (max: nat { min <= max } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vclist_payload min max p))
  [SMTPat   (and_then_cases_injective (parse_vclist_payload min max p))]
=
    and_then_cases_injective_intro #(bounded_count min max) (parse_vclist_payload min max p) (fun x1 x2 b1 b2 ->
    parse_synth_eq (parse_nlist (U32.v x1) p) (synth_vclist_payload min max x1) b1;
    parse_synth_eq (parse_nlist (U32.v x2) p) (synth_vclist_payload min max x2) b2
  )

let parse_vclist
  (min: nat)
  (max: nat { min <= max } )
  (#lk: parser_kind)
  (lp: parser lk U32.t)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_vclist_kind min max lk k) (vlarray t min max))
= ((lp `parse_filter` bounded_count_prop min max) `parse_synth` synth_bounded_count min max) `and_then` parse_vclist_payload min max p 

let parse_vclist_eq
  (min: nat)
  (max: nat { min <= max } )
  (#lk: parser_kind)
  (lp: parser lk U32.t)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma
  (parse (parse_vclist min max lp p) b == (match parse lp b with
  | None -> None
  | Some (n, consumed_n) ->
    if min <= U32.v n && U32.v n <= max
    then
      let b_payload = Seq.slice b consumed_n (Seq.length b) in
      match parse (parse_nlist (U32.v n) p) b_payload with
      | None -> None
      | Some (l, consumed_l) ->
        Some (l, consumed_n + consumed_l)
    else None
  ))
= and_then_eq ((lp `parse_filter` bounded_count_prop min max) `parse_synth` synth_bounded_count min max) (parse_vclist_payload min max p) b;
  parse_synth_eq (lp `parse_filter` bounded_count_prop min max) (synth_bounded_count min max) b;
  parse_filter_eq lp (bounded_count_prop min max) b;
  match parse lp b with
  | None -> ()
  | Some (n, consumed_n) ->
    if min <= U32.v n && U32.v n <= max
    then
      let b_payload = Seq.slice b consumed_n (Seq.length b) in
      let n : bounded_count min max = n in
      parse_synth_eq #_ #(nlist (U32.v n) t) #(vlarray t min max) (parse_nlist (U32.v n) p) (synth_vclist_payload min max n) b_payload
    else ()

let bare_serialize_vclist
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (l: vlarray t min max)
: GTot bytes
= let n = L.length l in
  let un = U32.uint_to_t n in
  serialize ls un `Seq.append` serialize (serialize_nlist n s) l

let bare_serialize_vclist_correct
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp  { lk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Lemma
  (serializer_correct (parse_vclist min max lp p) (bare_serialize_vclist min max ls s))
= let prf (x: vlarray t min max)
  : Lemma
    (let fx = bare_serialize_vclist min max ls s x in
      parse (parse_vclist min max lp p) fx == Some (x, Seq.length fx))
  = let fx = bare_serialize_vclist min max ls s x in
    parse_vclist_eq min max lp p fx;
    let n = L.length x in
    let un = U32.uint_to_t n in
    let fn = serialize ls un in
    parse_strong_prefix lp fn fx;
    let fl = serialize (serialize_nlist n s) x in
    assert (fl `Seq.equal` Seq.slice fx (Seq.length fn) (Seq.length fx))
  in
  Classical.forall_intro prf

let serialize_vclist
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp  { lk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (serializer (parse_vclist min max lp p))
= [@inline_let] let _ = bare_serialize_vclist_correct min max ls s in
  bare_serialize_vclist min max ls s
