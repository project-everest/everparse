module Parquet.Spec.Toplevel

module U32 = FStar.UInt32

module U8 = FStar.UInt8

module I8 = FStar.Int8

module I16 = FStar.Int16

module I32 = FStar.Int32

module I64 = FStar.Int64

module Seq = FStar.Seq

module List = FStar.List

open LowParse.Spec.Base

open LowParse.Spec.RtoLDepPair

open LowParse.Spec.RtoLPair

open LowParse.Spec.Combinators

open LowParse.Spec.SeqBytes

open LowParse.Spec.BoundedInt

open LowParse.Bytes

open FStar.Real

open FStar.List.Tot

include Parquet.Spec.Toplevel.Types


(* Another separate pass to check offset_index and column_index *)
(* They don't overlap with the footer metadata *)

(*
  File: A HDFS file that must include the metadata for the file. It does not need to actually contain the data.

  Row group: A logical horizontal partitioning of the data into rows. There is no physical structure that is guaranteed for a row group. A row group consists of a column chunk for each column in the dataset.

  Column chunk: A chunk of the data for a particular column. They live in a particular row group and are guaranteed to be contiguous in the file.

  Page: Column chunks are divided up into pages. A page is conceptually an indivisible unit (in terms of compression and encoding). There can be multiple page types which are interleaved in a column chunk.

  Hierarchically, a file consists of one or more row groups. A row group contains exactly one column chunk per column. Column chunks contain one or more pages.

  1. Check offset_index and column_index (They don't overlap with the footer metadata)
  2. Check the correctness of all the offsets and sizes (disjointness among all pages)
  3. Check the order (page locations per column chunk)
  4. Check that the sizes of children should add up to the same size of the parents
  5. Check the list schema_element is of the same tree structure of the rowgroup's list column_chunk
  6. Check the physical types of column_meta_data against the schema
  7. Check the actual data value against the phycial/logical type (will be slow, except for e.g., ints)
  8. Statistics can be checked, but only for optimization (to skip pages efficiently)
 *)
// val validate_file_metat_data (fmd: file_meta_data) : bool

// let validate_file_metat_data (fmd: file_meta_data) : bool = true

(** Helpers ----------------------------------------------------------- *)

let rec zip (#a #b: Type0) (xs: list a) (ys: list b {List.length ys == List.length xs})
    : Tot (list (a & b)) =
  match xs, ys with
  | [], [] -> []
  | x :: xs', y :: ys' -> (x, y) :: (zip xs' ys')



(* A byte‑range in the file *)

type range = {
  start:int;
  len:int
}

let range_end (r: range) : int = r.start + r.len



(* Two ranges are disjoint iff they don’t overlap *)

let disjoint (r1 r2: range) : Tot bool =
  let end1 = range_end r1 in
  let end2 = range_end r2 in
  (r1.start >= end2) || (r2.start >= end1)


(* Check if a list of ranges are disjoint *)

let rec ranges_disjoint (rs: list range) : Tot bool =
  match rs with
  | [] | [_] -> true
  | x :: xs -> List.Tot.for_all (disjoint x) xs && ranges_disjoint xs



(** Validation of a single column‑chunk ------------------------------ *)

val validate_column_chunk: column_chunk -> Tot bool

let validate_column_chunk cc =
  let offsets_ok =
    // dictionary_page, if present, should be the first in every column
    match cc.meta_data with
    | None -> true
    | Some cmd ->
      let data_off = I64.v cmd.data_page_offset in
      begin match cmd.dictionary_page_offset with
      | None -> true
      | Some dict_off ->
        I64.v dict_off < data_off &&
        begin match cmd.index_page_offset with
        | None -> true
        | Some idx_off -> I64.v dict_off < I64.v idx_off
        end
      end
  in
  let idx_ok:// OffsetIndex may be present even if ColumnIndex is not.
  // If ColumnIndex is present, OffsetIndex must also be present.
  // If offset is present, the corresponding length must be present
  bool =
    (Some? cc.offset_index_offset = Some? cc.offset_index_length) &&
    (Some? cc.column_index_offset = Some? cc.column_index_length) &&
    (if Some? cc.column_index_offset then Some? cc.offset_index_offset else true)
  in
  offsets_ok && idx_ok



(** Column order vs schema order ------------------------------------- *)

// type schema_tree = 
//   | Leaf of schema_element
//   | Node of schema_element & list schema_tree
//
// (* Build a schema tree from the flat list.
//  * The flat list was built based on depth-first traversal of the tree
//  *)
// val build_schema_tree : list schema_element -> Tot (option schema_tree)
//
// let rec build_schema_tree : list schema_element -> Tot (option schema_tree) = 

(** ------------------------------------------------------------------ *)
(**  Schema‑tree reconstruction                                         *)
(** ------------------------------------------------------------------ *)

(* A tree view of the flattened SchemaElement list *)

type schema_tree =
  | Leaf : schema_element -> schema_tree
  | Node : se: schema_element -> children: list schema_tree -> schema_tree



(* Internal helper: consume a prefix of the list, returning the
   subtree and the unconsumed suffix. The input list MUST encode a
   well‑formed schema (depth‑first order, correct num_children.) *)
// let rec build_aux (els:list schema_element)
//   : Tot (option (schema_tree * list schema_element))
//   (decreases els)
//   = match els with
//     | [] -> None
//     | hd::tl ->
//         let nc = match hd.num_children with | Some n -> I32.v n | None -> 0 in
//         if nc = 0 then Some (Leaf hd, tl)
//         else
//           (* build [nc] children sequentially *)
//           // make it top-level mutually recursive function
//           let (kids, rem) = collect nc tl [] in
//           Some (Node hd kids, rem)
// and collect k (rest:list schema_element)
//   (acc:list schema_tree)
//   : Tot (list schema_tree * list schema_element) 
//   (decreases k, rest)
//   =
//   if k = 0 then (List.Tot.rev acc, rest) else
//   match build_aux rest with
//   | None -> (List.Tot.rev acc, rest) // not enough elements to build a child
//   | Some (child, rest') ->
//     collect (k - 1) rest' (child :: acc)
  // let (child, rest') = build_aux rest in
  // collect (k-1) rest' (child::acc)


// val build_schema_tree : list schema_element -> Tot (option schema_tree)
// let build_schema_tree els =
//   // let (tree, rest) = build_aux els in
//   match build_aux els with
//   | None -> None
//   | Some (tree, rest) ->
//   if List.Tot.length rest = 0 then Some tree
//   else 
//     // the input list was not well-formed
//     None

(** Row‑group validation --------------------------------------------- *)

(* Calculate the total size of all column chunks in a row group *)

let rec cols_size (ccs: list column_chunk) : option int =
  match ccs with
  | [] -> Some 0
  | cc :: q ->
    match cc.meta_data with
    | None -> None
    | Some md ->
      match cols_size q with
      | None -> None
      | Some sz -> Some (I64.v md.total_compressed_size + sz)


(* dictionary_page_offset ? dictionary_page_offset : min (index_page_offset, data_page_offset) *)

let offset_of_column_chunk (cmd: column_meta_data) : int64 =
  match cmd.dictionary_page_offset with
  | Some off -> off
  | None ->
    match cmd.index_page_offset with
    | Some off -> if I64.v off < I64.v cmd.data_page_offset then off else cmd.data_page_offset
    | None -> cmd.data_page_offset

module J = Parquet.Spec.Jump

let columns_are_sorted (cols: list column_chunk) : Tot bool =
  J.offsets_and_sizes_are_sorted
   (List.Tot.map
     (fun col -> 
       match col.meta_data with
       | Some col -> (I64.v (offset_of_column_chunk col), I64.v col.total_compressed_size)
       | _ -> (0, 0) (* dummy *)
     )
     cols
   )

let first_column_offset
  (rg: row_group)
: Tot (option _)
=
    // column offset is the first page offset
    match rg.columns with
    | [] -> None
    | first :: _ ->
      match first.meta_data with
      | None -> None
      | Some cmd -> Some (offset_of_column_chunk cmd)

let validate_row_group_aux (rg: row_group) : Tot bool =
  let sorted_ok =
    if List.Tot.for_all (fun c -> Some? c.meta_data) rg.columns then
    (* cols should be contiguous according to the documentation, but we found some counterexamples, so we relax the requirement to cols being sorted *)
    columns_are_sorted rg.columns
    else true
  in
  let cols_ok =
    List.Tot.for_all validate_column_chunk rg.columns (* each column chunk passes *)
  in
  sorted_ok && cols_ok

let column_size_nonnegative
  (cc: column_chunk)
: Tot bool
= match cc.meta_data with
  | None -> true
  | Some md -> I64.v md.total_compressed_size >= 0

let validate_row_group_size (data_size: I64.t) (rg: row_group) : Tot bool =
    (* sum of col sizes equals row‑group size (when available) *)
  List.Tot.for_all column_size_nonnegative rg.columns &&
  begin
    let total_row_size = match rg.total_compressed_size with
    | None -> data_size
    | Some sz -> sz
    in
    I64.v total_row_size <= I64.v data_size &&
    begin
      let total_size = cols_size rg.columns in
      (* total_size is None if any column chunk is missing metadata *)
      (* so we can’t check the size *)
      match total_size with
      | None -> true
      | Some total_sz -> total_sz <= (* should be =, but column chunks are not contiguous, see below *) I64.v total_row_size
    end
  end

val validate_row_group : I64.t -> row_group -> Tot bool

let validate_row_group data_size rg =
  validate_row_group_size data_size rg &&
  validate_row_group_aux rg

let rg_range (rg: row_group) : option range =
  match first_column_offset rg, rg.total_compressed_size with
  | Some off, Some sz -> Some ({ start = I64.v off; len = I64.v sz })
  | _ ->
    let total_size = cols_size rg.columns in
    match rg.columns with
    | [] -> None
    | first :: _ ->
      match first.meta_data with
      | None -> None
      | Some cmd ->
        match total_size with
        | None -> None
        | Some total_sz -> Some ({ start = I64.v (offset_of_column_chunk cmd); len = total_sz })


(** Top‑level file metadata validation ------------------------------- *)

let rec list_option_map (#t1 #t2: Type) (f: (t1 -> option t2)) (l: list t1) : Tot (list t2) =
  match l with
  | [] -> []
  | a :: q ->
    let q' = list_option_map f q in
    begin match f a with
    | None -> q'
    | Some a' -> a' :: q'
    end

val validate_file_meta_data: nat -> file_meta_data -> Tot bool

let validate_file_meta_data footer_start fmd =
  FStar.Int.fits footer_start 64 &&
  ranges_disjoint (list_option_map rg_range fmd.row_groups) &&
  List.Tot.for_all (validate_row_group (I64.int_to_t footer_start)) fmd.row_groups

let page_offsets_are_contiguous (locs: list page_location) : Tot bool =
  J.offsets_and_sizes_are_contiguous
    (List.Tot.map (fun loc -> ((I64.v loc.offset <: int), (I32.v loc.compressed_page_size <: int))) locs)


(* Once jump to OffsetIndex, validate its structure against the corresponding column_chunk *)

val validate_offset_index (cc: column_chunk) (oi: offset_index) : Tot bool

let validate_offset_index (cc: column_chunk) (oi: offset_index) : Tot bool =
  let locs = oi.page_locations in
  let first_loc =
    // the first page location must be consistent with the (computed) page location in cc
    match locs with
    | [] -> None
    | first :: _ -> Some first
  in
  let first_page_offset =
    match cc.meta_data with
    | None -> None
    | Some cmd -> Some (I64.v (offset_of_column_chunk cmd))
  in
  let first_loc_ok =
    match first_loc, first_page_offset with
    | Some loc, Some off -> I64.v loc.offset = off
    | _ -> true
  in
  let cc_page_offsets_ok =
    // all page offsets (if present) in cc should be listed in `page_locations`
    match cc.meta_data with
    | None -> true
    | Some cmd ->
      let all_page_offsets = List.Tot.map (fun pl -> pl.offset) locs in
      let contains (off: int64) = List.Tot.mem off all_page_offsets in
      begin match cmd.dictionary_page_offset with
      | Some dict_off -> contains dict_off
      | None -> true
      end && begin match cmd.index_page_offset with
      | Some idx_off -> contains idx_off
      | None -> true
      end &&
      contains cmd.data_page_offset
  in
  let col_size_ok =
    //compressed size matches meta
    match cc.meta_data with
    | None -> true
    | Some md ->
      let s = List.Tot.fold_left (fun acc pl -> acc + I32.v pl.compressed_page_size) 0 locs in
      s = I64.v md.total_compressed_size
  in
  let contiguous_ok =
    page_offsets_are_contiguous locs
  in
  // let ordered =
  //   (* ordered by offset and disjoint *)
  //   match locs with
  //   | [] -> true
  //   | first :: rest -> offsets_are_ordered first rest
  // in
  // let disj =
  //   let pl_ranges =
  //     List.Tot.map (fun pl -> { start = I64.v pl.offset; len = I32.v pl.compressed_page_size }) locs
  //   in
  //   ranges_disjoint pl_ranges
  // in
  // first_loc_ok && col_size_ok && ordered && disj
  first_loc_ok && cc_page_offsets_ok && col_size_ok && contiguous_ok




assume
val parse_footer_kind:parser_kind

// assume
// val footer_t:Type0

assume
val parse_footer:parser parse_footer_kind file_meta_data
// val parse_footer:parser parse_footer_kind footer_t

assume
val serialize_footer:serializer parse_footer
// val parse_footer:parser parse_footer_kind footer_t

let is_PAR1 (s: Seq.lseq byte 4) : bool =
  let v0 = Seq.index s 0 in
  let v1 = Seq.index s 1 in
  let v2 = Seq.index s 2 in
  let v3 = Seq.index s 3 in
  (U32.v (FStar.Char.u32_of_char 'P') = U8.v v0) && 
  (U32.v (FStar.Char.u32_of_char 'A') = U8.v v1) &&
  (U32.v (FStar.Char.u32_of_char 'R') = U8.v v2) &&
  (U32.v (FStar.Char.u32_of_char '1') = U8.v v3)

assume
val parse_offset_index_kind: parser_kind

assume
val parse_offset_index: tot_parser parse_offset_index_kind offset_index

assume
val serialize_offset_index : tot_serializer parse_offset_index

assume
val parse_page_header_kind: (k: parser_kind { k.parser_kind_subkind == Some ParserStrong })

assume
val parse_page_header: tot_parser parse_page_header_kind page_header

assume
val serialize_page_header: tot_serializer parse_page_header

let validate_page_data (h: page_header) (d: bytes) : Tot bool =
  I32.v h.compressed_page_size = Seq.length d &&
  true (* TODO: validate data against schema *)

let tot_parse_page = tot_parse_dtuple2 parse_page_header (fun h -> tot_parse_filter tot_parse_seq_all_bytes (validate_page_data h))

let parse_page = parse_dtuple2 (parser_of_tot_parser parse_page_header) (fun h -> parse_filter parse_seq_all_bytes (validate_page_data h))

let parse_page_equiv' (b: bytes) : Lemma
  (parse (parser_of_tot_parser tot_parse_page) b == parse parse_page b)
= parse_dtuple2_eq (parser_of_tot_parser parse_page_header) (fun h -> parse_filter parse_seq_all_bytes (validate_page_data h)) b;
  match parse (parser_of_tot_parser parse_page_header) b with
  | None -> ()
  | Some (ph, consumed) ->
    let b' = Seq.slice b consumed (Seq.length b) in
    parse_filter_eq parse_seq_all_bytes (validate_page_data ph) b'

let parse_page_equiv : squash (forall b . parse (parser_of_tot_parser tot_parse_page) b == parse parse_page b) = Classical.forall_intro parse_page_equiv'

let validate_page_location_all (data: bytes) (pl: page_location) : Tot bool =
      I64.v pl.offset >= 0 &&
      I32.v pl.compressed_page_size >= 0 &&
      J.pred_jump_with_offset_and_size_then_parse
        (I64.v pl.offset)
        (I32.v pl.compressed_page_size)
        tot_parse_page
        data

let validate_offset_index_all_aux (data: bytes) (oi: offset_index) : Tot bool =
  List.Tot.for_all
    (validate_page_location_all data)
    oi.page_locations

let validate_offset_index_all (cc: column_chunk) (data: bytes) (oi: offset_index) : Tot bool =
  validate_offset_index cc oi &&
  validate_offset_index_all_aux data oi

let validate_all_validate_column_chunk
  (data: bytes)
  (cc: column_chunk)
: Tot bool
=
          match cc.offset_index_offset, cc.offset_index_length with
          | Some offset, Some length ->
            I64.v offset >= 0 &&
            I32.v length >= 0 &&
            J.pred_jump_with_offset_and_size_then_parse
              (I64.v offset)
              (I32.v length)
              (tot_parse_filter
                parse_offset_index
                (validate_offset_index_all cc data)
              )
              data
          | _ -> true

let validate_all_validate_row_group
  (data: bytes)
  (rg: row_group)
: Tot bool
= List.Tot.for_all (validate_all_validate_column_chunk data) rg.columns

let validate_all (fmd: file_meta_data) (data: bytes) : Tot bool =
  validate_file_meta_data (Seq.length data) fmd &&
  J.pred_jump_with_offset_and_size_then_parse 0 4 (tot_parse_filter (tot_parse_seq_flbytes 4) is_PAR1) data &&
  List.Tot.for_all (validate_all_validate_row_group data) fmd.row_groups

let parse_parquet =
  parse_nondep_then_rtol (parse_filter (parse_seq_flbytes 4) is_PAR1)
    (parse_dtuple2_rtol parse_u32_le
        (fun len ->
            (weaken (dtuple2_rtol_kind parse_seq_all_bytes_kind 0)
                (parse_dtuple2_rtol (parse_fldata_strong serialize_footer (U32.v len))
                    (fun footer ->
                        parse_filter parse_seq_all_bytes (validate_all footer)
                      )))))
