module Parquet.Spec.Jump
include LowParse.Spec.Base

open LowParse.Spec.FLData

module Seq = FStar.Seq

let coerce_ 
  (#t: Type)
  (#new_b: bytes)
  (#b: bytes { Seq.length b >= Seq.length new_b })
  (x: option (t & consumed_length new_b))
: option (t & consumed_length b)
  = match x with
    | None -> None
    | Some (v, l) -> Some (v, l)

val jump_with_offset_and_size_then_parse
  (offset: nat)
  (size: nat)
  (#t: Type)
  (p: tot_bare_parser t)
// : Tot (parser (parse_fldata_kind size k) t)
: Tot (tot_bare_parser t)

inline_for_extraction
val tot_parse_fldata'
  (#t: Type)
  (p: tot_bare_parser t)
  (sz: nat)
: Tot (tot_bare_parser t)

let tot_parse_fldata' #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, (sz <: consumed_length s))
      else None
    | _ -> None

let jump_with_offset_and_size_then_parse
  (offset: nat)
  (size: nat)
  (#t: Type)
  (p: tot_bare_parser t)
: Tot (tot_bare_parser t)
// : Tot (parser (parse_fldata_kind size k) t)
  = fun b ->
    if Seq.length b < offset + size then
      None
    else
      let new_b = Seq.slice b offset (offset + size) in
      coerce_ ((tot_parse_fldata' p size) new_b)

let pred_jump_with_offset_and_size_then_parse
  (offset: nat)
  (size: nat)
  (#t: Type)
  (p: tot_bare_parser t)
  (b: bytes)
: Tot bool
= Some? (jump_with_offset_and_size_then_parse offset size p b)

let andp_g (#t: Type) (g1 g2: (t -> GTot bool)) (x: t) : GTot bool =
  g1 x && g2 x

let rec offsets_and_sizes_are_contiguous
  (l: list (nat & nat))
: Tot bool
= match l with
  | (off1, sz1) :: (off2, sz2) :: q ->
    off1 + sz1 = off2 &&
    offsets_and_sizes_are_contiguous ((off2, sz2) :: q)
  | _ -> true

let rec offsets_and_sizes_are_sorted
  (l: list (nat & nat))
: Tot bool
= match l with
  | (off1, sz1) :: (off2, sz2) :: q ->
    off1 + sz1 <= off2 &&
    offsets_and_sizes_are_sorted ((off2, sz2) :: q)
  | _ -> true

let rec offsets_and_sizes_are_contiguous_implies_sorted
  (l: list (nat & nat))
: Lemma
  (requires (offsets_and_sizes_are_contiguous l))
  (ensures (offsets_and_sizes_are_sorted l))
= match l with
  | (off1, sz1) :: (off2, sz2) :: q ->
    offsets_and_sizes_are_contiguous_implies_sorted ((off2, sz2) :: q)
  | _ -> ()

let rec offsets_and_sizes_are_sorted_disjoint
  (l: list (nat & nat))
  (i1 i2: nat)
: Lemma
  (requires (
    offsets_and_sizes_are_sorted l /\
    i1 < i2 /\
    i2 < List.Tot.length l
  ))
  (ensures (
    let (off1, sz1) = List.Tot.index l i1 in
    let (off2, _) = List.Tot.index l i2 in
    off1 + sz1 <= off2
  ))
  (decreases (List.Tot.length l))
= if i1 = 0 then begin
    let (off1, sz1) :: (off15, sz15) :: q = l in
    if i2 = 1 then () else 
    offsets_and_sizes_are_sorted_disjoint ((off1, off15 - off1 + sz15) :: q) 0 (i2 - 1)
  end
  else offsets_and_sizes_are_sorted_disjoint (List.Tot.tl l) (i1 - 1) (i2 - 1)
