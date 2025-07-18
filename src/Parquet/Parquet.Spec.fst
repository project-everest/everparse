module Parquet.Spec

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

assume
val parse_footer_kind:parser_kind

assume
val footer_t:Type0

assume
val parse_footer:parser parse_footer_kind footer_t

assume
val parse_pages_kind:parser_kind

assume
val pages_t (footer: footer_t) : Type0

assume
val parse_pages (footer: footer_t) : parser parse_pages_kind (pages_t footer)

let is_PAR1 (s: Seq.lseq byte 4) : bool =
  let v0 = Seq.index s 0 in
  let v1 = Seq.index s 1 in
  let v2 = Seq.index s 2 in
  let v3 = Seq.index s 3 in
  (U32.v (FStar.Char.u32_of_char 'P') = U8.v v0) && (U32.v (FStar.Char.u32_of_char 'A') = U8.v v1) &&
  (U32.v (FStar.Char.u32_of_char 'R') = U8.v v2) &&
  (U32.v (FStar.Char.u32_of_char '1') = U8.v v3)

let parse_parquet =
  parse_nondep_then_rtol (parse_filter (parse_seq_flbytes 4) is_PAR1)
    (parse_dtuple2_rtol parse_u32_le
        (fun len ->
            (weaken (dtuple2_rtol_kind parse_seq_all_bytes_kind 0)
                (parse_dtuple2_rtol (parse_fldata parse_footer (U32.v len))
                    (fun footer ->
                      // parse_pages footer
                      (parse_seq_all_bytes))))))



// Enumerated Types

type physical_type =
  | BOOLEAN
  | INT32
  | INT64
  | INT96
  | FLOAT
  | DOUBLE
  | BYTE_ARRAY
  | FIXED_LEN_BYTE_ARRAY

type converted_type =
  | DEPRECATED_UTF8
  | DEPRECATED_MAP
  | DEPRECATED_MAP_KEY_VALUE
  | DEPRECATED_LIST
  | DEPRECATED_ENUM
  | DEPRECATED_DECIMAL
  | DEPRECATED_DATE
  | DEPRECATED_TIME_MILLIS
  | DEPRECATED_TIME_MICROS
  | DEPRECATED_TIMESTAMP_MILLIS
  | DEPRECATED_TIMESTAMP_MICROS
  | DEPRECATED_UINT_8
  | DEPRECATED_UINT_16
  | DEPRECATED_UINT_32
  | DEPRECATED_UINT_64
  | DEPRECATED_INT_8
  | DEPRECATED_INT_16
  | DEPRECATED_INT_32
  | DEPRECATED_INT_64
  | DEPRECATED_JSON
  | DEPRECATED_BSON
  | DEPRECATED_INTERVAL

type field_repetition_type =
  | REQUIRED
  | OPTIONAL
  | REPEATED

type encoding =
  | PLAIN
  | PLAIN_DICTIONARY
  | RLE
  | BIT_PACKED
  | DELTA_BINARY_PACKED
  | DELTA_LENGTH_BYTE_ARRAY
  | DELTA_BYTE_ARRAY
  | RLE_DICTIONARY
  | BYTE_STREAM_SPLIT

type compression_codec =
  | UNCOMPRESSED
  | SNAPPY
  | GZIP
  | LZO
  | BROTLI
  | LZ4
  | ZSTD
  | LZ4_RAW

type page_type =
  | DATA_PAGE
  | INDEX_PAGE
  | DICTIONARY_PAGE
  | DATA_PAGE_V2

type boundary_order =
  | UNORDERED
  | ASCENDING
  | DESCENDING

type edge_interpolation_algorithm =
  | SPHERICAL
  | VINCENTY
  | THOMAS
  | ANDOYER
  | KARNEY



// Statistics and Metadata Structures

type int64 = I64.t

type int32 = I32.t

type int16 = I16.t

type int8 = I8.t

type size_statistics = {
  unencoded_byte_array_data_bytes:option int64;
  repetition_level_histogram:option (list int64);
  definition_level_histogram:option (list int64)
}

noeq
type bounding_box = {
  xmin:real;
  xmax:real;
  ymin:real;
  ymax:real;
  zmin:option real;
  zmax:option real;
  mmin:option real;
  mmax:option real
}

noeq
type geospatial_statistics = {
  bbox:option bounding_box;
  geospatial_types:option (list int32)
}

type statistics = {
  max:option bytes;
  min:option bytes;
  null_count:option int64;
  distinct_count:option int64;
  max_value:option bytes;
  min_value:option bytes;
  is_max_value_exact:option bool;
  is_min_value_exact:option bool
}



// Logical Types

type string_type = unit

type uuid_type = unit

type map_type = unit

type list_type = unit

type enum_type = unit

type date_type = unit

type float16_type = unit

type null_type = unit

type json_type = unit

type bson_type = unit

type decimal_type = {
  scale:int32;
  precision:int32
}

type milli_seconds = unit

type micro_seconds = unit

type nano_seconds = unit

type time_unit =
  | MILLIS of milli_seconds
  | MICROS of micro_seconds
  | NANOS of nano_seconds

type timestamp_type = {
  isAdjustedToUTC:bool;
  unit:time_unit
}

type time_type = {
  isAdjustedToUTC:bool;
  unit:time_unit
}

type int_type = {
  bitWidth:int8;
  isSigned:bool
}

type variant_type = { specification_version:option int8 }

type geometry_type = { crs:option string }

type geography_type = {
  crs:option string;
  algorithm:option edge_interpolation_algorithm
}

type logical_type =
  | STRING of string_type
  | MAP of map_type
  | LIST of list_type
  | ENUM of enum_type
  | DECIMAL of decimal_type
  | DATE of date_type
  | TIME of time_type
  | TIMESTAMP of timestamp_type
  | INTEGER of int_type
  | UNKNOWN of null_type
  | JSON of json_type
  | BSON of bson_type
  | UUID of uuid_type
  | FLOAT16 of float16_type
  | VARIANT of variant_type
  | GEOMETRY of geometry_type
  | GEOGRAPHY of geography_type



// Schema elements

type schema_element = {
  type_:option physical_type;
  type_length:option int32;
  repetition_type:option field_repetition_type;
  name:string;
  num_children:option int32;
  converted_type:option converted_type;
  scale:option int32;
  precision:option int32;
  field_id:option int32;
  logical_type:option logical_type
}



// Page structures

type data_page_header = {
  num_values:int32;
  encoding_:encoding;
  definition_level_encoding:encoding;
  repetition_level_encoding:encoding;
  statistics:option statistics
}

type index_page_header = unit

type dictionary_page_header = {
  num_values:int32;
  encoding:encoding;
  is_sorted:option bool
}

type data_page_header_v2 = {
  num_values:int32;
  num_nulls:int32;
  num_rows:int32;
  encoding:encoding;
  definition_levels_byte_length:int32;
  repetition_levels_byte_length:int32;
  is_compressed:option bool;
  statistics:option statistics
}



// Bloom Filters

type split_block_algorithm = unit

type bloom_filter_algorithm = | BLOCK of split_block_algorithm

type xx_hash = unit

type bloom_filter_hash = | XXHASH of xx_hash

type uncompressed = unit

type bloom_filter_compression = | UN_COMPRESSED of uncompressed

type bloom_filter_header = {
  numBytes:int32;
  algorithm:bloom_filter_algorithm;
  hash:bloom_filter_hash;
  compression:bloom_filter_compression
}



// Column chunks

// type page_header_variants =
//   | DATA_PAGE_HEADER of data_page_header
//   | INDEX_PAGE_HEADER of index_page_header
//   | DICTIONARY_PAGE_HEADER of dictionary_page_header
//   | DATA_PAGE_HEADER_V2 of data_page_header_v2

type page_header = {
  ptype:page_type;
  uncompressed_page_size:int32;
  compressed_page_size:int32;
  crc:option int32;
  data_page_header:option data_page_header;
  index_page_header:option index_page_header;
  dictionary_page_header:option dictionary_page_header;
  data_page_header_v2:option data_page_header_v2
}



// header:page_header_variants // sum type instead of "tagged union"

type key_value = {
  key:string;
  value:option string
}

type sorting_column = {
  column_idx:int32;
  descending:bool;
  nulls_first:bool
}

type page_encoding_stats = {
  page_type:page_type;
  encoding:encoding;
  count:int32
}

noeq
type column_meta_data = {
  physical_type:physical_type;
  encodings:list encoding;
  path_in_schema:list string;
  codec:compression_codec;
  num_values:int64;
  total_uncompressed_size:int64;
  total_compressed_size:int64;
  key_value_metadata:option (list key_value);
  data_page_offset:int64;
  index_page_offset:option int64;
  dictionary_page_offset:option int64;
  statistics:option statistics;
  encoding_stats:option (list page_encoding_stats);
  bloom_filter_offset:option int64;
  bloom_filter_length:option int32;
  size_statistics:option size_statistics;
  geospatial_statistics:option geospatial_statistics
}

type encryption_with_footer_key = unit

type encryption_with_column_key = {
  path_in_schema:list string;
  key_metadata:option string
}

type column_crypto_meta_data =
  | ENCRYPTION_WITH_FOOTER_KEY of encryption_with_footer_key
  | ENCRYPTION_WITH_COLUMN_KEY of encryption_with_column_key

noeq
type column_chunk = {
  file_path:option string;
  file_offset:int64;
  meta_data:option column_meta_data; // can be required for featherweight parquet
  offset_index_offset:option int64;
  offset_index_length:option int32;
  column_index_offset:option int64;
  column_index_length:option int32;
  crypto_metadata:option column_crypto_meta_data;
  encrypted_column_metadata:option string
}

noeq
type row_group = {
  columns:list column_chunk;
  total_byte_size:int64;
  num_rows:int64;
  sorting_columns:option (list sorting_column);
  file_offset:option int64;
  total_compressed_size:option int64;
  ordinal:option int16
}

type type_defined_order = unit

type column_order = | TYPE_ORDER of type_defined_order

type page_location = {
  offset:int64;
  compressed_page_size:int32;
  first_row_index:int64
}

type offset_index = {
  page_locations:list page_location;
  unencoded_byte_array_data_bytes:option (list int64)
}

type column_index = {
  null_pages:list bool;
  min_values:list string;
  max_values:list string;
  boundary_order:boundary_order;
  null_counts:option (list int64);
  repetition_level_histograms:option (list int64);
  definition_level_histograms:option (list int64)
}

type aes_gcm_v1 = {
  aad_prefix:option string;
  aad_file_unique:option string;
  supply_aad_prefix:option bool
}

type aes_gcm_ctr_v1 = {
  aad_prefix:option string;
  aad_file_unique:option string;
  supply_aad_prefix:option bool
}

type encryption_algorithm =
  | AES_GCM_V1 of aes_gcm_v1
  | AES_GCM_CTR_V1 of aes_gcm_ctr_v1

noeq
type file_meta_data = {
  version:int32;
  schema:list schema_element;
  num_rows:int64;
  row_groups:list row_group;
  key_value_metadata:option (list key_value);
  created_by:option string;
  column_orders:option (list column_order);
  encryption_algorithm:option encryption_algorithm;
  footer_signing_key_metadata:option string
}

type file_crypto_meta_data = {
  encryption_algorithm:encryption_algorithm;
  key_metadata:option string
}



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



(* Check if a list of ranges are in-bound *)

let rec ranges_in_bound (rs: list range) (max_len: int) : Tot bool =
  match rs with
  | [] -> true
  | r :: rest ->
    let end_ = range_end r in
    end_ <= max_len && ranges_in_bound rest max_len



(* Check if a list of ranges are disjoint *)

let rec ranges_disjoint (rs: list range) : Tot bool =
  match rs with
  | [] | [_] -> true
  | x :: xs -> List.Tot.for_all (disjoint x) xs && ranges_disjoint xs

let rec offsets_are_ordered (prev: page_location) (locs: list page_location)
    : Tot bool (decreases locs) =
  match locs with
  | [] -> true
  | loc :: rest -> I64.v loc.offset >= I64.v prev.offset && offsets_are_ordered loc rest



(** Validation of a single column‑chunk ------------------------------ *)

val validate_column_chunk: column_chunk -> Tot bool

let validate_column_chunk cc =
  let offsets_ok =
    // dictionary_page, if present, should be the first in every column
    match cc.meta_data with
    | None -> true
    | Some cmd ->
      let data_off = I64.v cmd.data_page_offset in
      match cmd.dictionary_page_offset, cmd.index_page_offset with
      | None, _ -> true
      | Some dict_off, None -> I64.v dict_off < data_off
      | Some dict_off, Some idx_off -> I64.v dict_off < data_off && I64.v dict_off < I64.v idx_off
  in
  let idx_ok:// OffsetIndex may be present even if ColumnIndex is not.
  // If ColumnIndex is present, OffsetIndex must also be present.
  // If offset is present, the corresponding length must be present
  bool =
    match
      cc.offset_index_offset, cc.offset_index_length, cc.column_index_offset, cc.column_index_length
    with
    | Some _, Some _, Some _, Some _ | Some _, Some _, None, None | None, None, None, None -> true
    | _ -> false
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

let cols_size (ccs: list column_chunk) : option int =
  let col_sizes:list (option int64) =
    List.Tot.map (fun cc ->
          match cc.meta_data with
          | None -> None
          | Some md -> Some md.total_compressed_size)
      ccs
  in
  List.Tot.fold_left (fun acc sz_opt ->
        match acc, sz_opt with
        | Some acc_sz, Some sz -> Some (acc_sz + I64.v sz)
        | _, _ -> None)
    (Some 0)
    col_sizes



(* dictionary_page_offset ? dictionary_page_offset : min (index_page_offset, data_page_offset) *)

let offset_of_column_chunk (cmd: column_meta_data) : int64 =
  match cmd.dictionary_page_offset with
  | Some off -> off
  | None ->
    match cmd.index_page_offset with
    | Some off -> if I64.v off < I64.v cmd.data_page_offset then off else cmd.data_page_offset
    | None -> cmd.data_page_offset

let rec columns_are_contiguous (prev: column_chunk) (cols: list column_chunk)
    : Tot bool (decreases cols) =
  match cols with
  | [] -> true
  | cc :: rest ->
    match prev.meta_data, cc.meta_data with
    | Some (prev_md: column_meta_data), Some cc_md ->
      let prev_offset = I64.v (offset_of_column_chunk prev_md) in
      let cc_offset = I64.v (offset_of_column_chunk cc_md) in
      let prev_size = I64.v prev_md.total_compressed_size in
      prev_offset + prev_size = cc_offset && columns_are_contiguous cc rest
    | _ ->
      // if metadata is missing, we can't check contiguity
      true

val validate_row_group: row_group -> Tot bool

let validate_row_group rg =
  let col_offset =
    // column offset is the first page offset
    match rg.columns with
    | [] -> None
    | first :: _ ->
      match first.meta_data with
      | None -> None
      | Some cmd -> Some (offset_of_column_chunk cmd)
  in
  let offset_ok =
    match rg.file_offset with
    | None -> true
    | Some off ->
      match col_offset with
      | None -> true
      | Some col_off -> I64.v off = I64.v col_off
  in
  let rg_size_ok =
    (* sum of col sizes equals row‑group size (when available) *)
    match rg.total_compressed_size with
    | None -> true
    | Some sz ->
      let total_size = cols_size rg.columns in
      (* total_size is None if any column chunk is missing metadata *)
      (* so we can’t check the size *)
      match total_size with
      | None -> true
      | Some total_sz -> total_sz = I64.v sz
  in
  let contiguous_ok =
    (* cols should be contiguous *)
    match rg.columns with
    | [] -> true
    | first :: rest -> columns_are_contiguous first rest
  in
  let cols_ok =
    List.Tot.for_all (fun cc -> validate_column_chunk cc) rg.columns (* each column chunk passes *)
  in
  offset_ok && rg_size_ok && contiguous_ok && cols_ok

let cc_idx_ranges (cc: column_chunk) : list range =
  match
    cc.offset_index_offset, cc.offset_index_length, cc.column_index_offset, cc.column_index_length
  with
  | Some off, Some len, Some col_off, Some col_len ->
    let off_idx = { start = I64.v off; len = I32.v len } in
    let col_idx = { start = I64.v col_off; len = I32.v col_len } in
    [off_idx; col_idx]
  | Some off, Some len, None, None -> [{ start = I64.v off; len = I32.v len }]
  | _ -> []

let rg_range (rg: row_group) : option range =
  match rg.file_offset, rg.total_compressed_size with
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



// get a flat list of all page offsets

let get_all_page_offs (rgs: list row_group) : list int64 =
  List.Tot.collect (fun rg ->
        List.Tot.collect (fun cc ->
              match cc.meta_data with
              | None -> []
              | Some cmd ->
                let dict_off =
                  match cmd.dictionary_page_offset with
                  | None -> []
                  | Some off -> [off]
                in
                let idx_off =
                  match cmd.index_page_offset with
                  | None -> []
                  | Some off -> [off]
                in
                let data_off = [cmd.data_page_offset] in
                dict_off @ idx_off @ data_off)
          rg.columns)
    rgs

let rec page_offsets_are_distinct_and_inbound (page_offs: list int64) (bound: int64)
    : Tot bool (decreases page_offs) =
  match page_offs with
  | [] -> true
  | x :: xs ->
    not (List.Tot.contains x xs) && I64.v x < I64.v bound &&
    page_offsets_are_distinct_and_inbound xs bound



(** Top‑level file metadata validation ------------------------------- *)

val validate_file_meta_data: file_meta_data -> int64 -> Tot bool

let validate_file_meta_data fmd footer_start =
  let page_offs:// get a flat list of all page offsets
  list int64 =
    get_all_page_offs fmd.row_groups
  in
  let ranges:// get a flat list of all rg ranges and idx ranges
  list range =
    List.Tot.collect (fun rg ->
          let rg_range_opt = rg_range rg in
          let cc_ranges = List.Tot.collect cc_idx_ranges rg.columns in
          match rg_range_opt with
          | None -> cc_ranges
          | Some rg_range -> rg_range :: cc_ranges)
      fmd.row_groups
  in
  // page_offs should all be distinct and inbound
  page_offsets_are_distinct_and_inbound page_offs (footer_start) && ranges_disjoint ranges &&
  ranges_in_bound ranges
    // ranges should be mutually disjoint and non-overlapping with the footer
    (I64.v footer_start) &&
  List.Tot.for_all (fun rg -> validate_row_group rg) fmd.row_groups

let rec page_offsets_are_contiguous (prev: page_location) (locs: list page_location)
    : Tot bool (decreases locs) =
  match locs with
  | [] -> true
  | loc :: rest ->
    I64.v loc.offset = I64.v prev.offset + I32.v prev.compressed_page_size &&
    page_offsets_are_contiguous loc rest



(* Once jump to OffsetIndex, validate its structure against the corresponding column_chunk *)

val validate_offset_index (oi: offset_index) (cc: column_chunk) : Tot bool

let validate_offset_index (oi: offset_index) (cc: column_chunk) : Tot bool =
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
      let contains (off: int64) = List.Tot.contains off all_page_offsets in
      (match cmd.dictionary_page_offset, cmd.index_page_offset with
        | Some dict_off, Some idx_off -> contains dict_off && contains idx_off
        | Some dict_off, None -> contains dict_off
        | None, Some idx_off -> contains idx_off
        | None, None -> true) &&
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
    match locs with
    | [] -> true
    | first :: rest -> page_offsets_are_contiguous first rest
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
