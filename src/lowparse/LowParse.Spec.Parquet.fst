module LowParse.Spec.Parquet

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
  ptype: page_type;
  uncompressed_page_size:int32;
  compressed_page_size:int32;
  crc:option int32;
  data_page_header: option data_page_header;
  index_page_header: option index_page_header;
  dictionary_page_header: option dictionary_page_header;
  data_page_header_v2: option data_page_header_v2
  // header:page_header_variants // sum type instead of "tagged union"
}



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
  start:int64;
  len:int32
}

let range_end (r: range) : int = I64.v r.start + I32.v r.len



(* Two ranges are disjoint iff they don’t overlap *)

let disjoint (r1 r2: range) : Tot bool =
  let end1 = range_end r1 in
  let end2 = range_end r2 in
  (I64.v r1.start >= end2) || (I64.v r2.start >= end1)



(* Check if a list of ranges are disjoint *)

let rec ranges_disjoint (rs: list range) : Tot bool =
  match rs with
  | [] | [_] -> true
  | x :: xs -> List.Tot.for_all (disjoint x) xs && ranges_disjoint xs



(* Build a range from optional offset/length *)

let range_of_offsets (off: option int64) (len: option int32) : option range =
  match off, len with
  | Some o, Some l -> Some ({ start = o; len = l })
  | _ -> None



// (* Sum a list<int32> into int64 safely *)
// let sum_i32 (xs:list int32) : Tot int64 =
//   List.Tot.fold_left (fun acc x -> acc + int64 (v x)) 0L xs

let rec offsets_are_ordered (prev: page_location) (locs: list page_location)
    : Tot bool (decreases locs) =
  match locs with
  | [] -> true
  | loc :: rest -> I64.v loc.offset >= I64.v prev.offset && offsets_are_ordered loc rest



(** Validation of a single column‑chunk ------------------------------ *)

val validate_column_chunk: column_chunk -> int64 -> option offset_index -> Tot bool

let validate_column_chunk cc footer_start oi =
  let idx_ranges:(* 1. index ranges must be disjoint and not overlap with footer *)
  list range =
    let off_idx = range_of_offsets cc.offset_index_offset cc.offset_index_length in
    let col_idx = range_of_offsets cc.column_index_offset cc.column_index_length in
    match off_idx, col_idx with
    | Some r1, Some r2 -> [r1; r2]
    | Some r, None | None, Some r -> [r]
    | None, None -> []
  in
  let idx_ok =
    ranges_disjoint idx_ranges &&
    List.Tot.for_all (fun r -> range_end r <= I64.v footer_start) idx_ranges
  in
  let pages_ok =
    (* 2. page‑level checks when we have an OffsetIndex *)
    match oi with
    | None -> true
    | Some oi' ->
      let locs = oi'.page_locations in
      let ordered =
        (* ordered by offset and disjoint *)
        match locs with
        | [] -> true
        | first :: rest -> offsets_are_ordered first rest
      in
      let disj =
        let pl_ranges =
          List.Tot.map (fun pl -> { start = pl.offset; len = pl.compressed_page_size }) locs
        in
        ranges_disjoint pl_ranges
      in
      let col_size_ok =
        (* compressed size matches meta *)
        match cc.meta_data with
        | None -> true
        | Some md ->
          let s = List.Tot.fold_left (fun acc pl -> acc + I32.v pl.compressed_page_size) 0 locs in
          s = I64.v md.total_compressed_size
      in
      ordered && disj && col_size_ok
  in
  idx_ok && pages_ok



(** Column order vs schema order ------------------------------------- *)

(** Row‑group validation --------------------------------------------- *)

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

val validate_row_group: row_group -> int64 -> list (option offset_index) -> Tot bool

let validate_row_group rg footer_start offset_indices =
  let col_sizes:(* sum of col sizes equals row‑group size (when available) *)
  list (option int64) =
    List.Tot.map (fun cc ->
          match cc.meta_data with
          | None -> None
          | Some md -> Some md.total_compressed_size)
      rg.columns
  in
  let rg_size_ok =
    match rg.total_compressed_size with
    | None -> true
    | Some sz ->
      let total_size =
        List.Tot.fold_left (fun acc sz_opt ->
              match acc, sz_opt with
              | Some acc_sz, Some sz -> Some (acc_sz + I64.v sz)
              | _, _ -> None)
          (Some 0)
          col_sizes
      in
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
    (* each column chunk passes *)
    if List.length offset_indices = List.length rg.columns
    then
      List.Tot.for_all (fun (cc, oi) -> validate_column_chunk cc footer_start oi)
        (zip rg.columns offset_indices)
    else false
  in
  rg_size_ok && contiguous_ok && cols_ok



(** Top‑level file metadata validation ------------------------------- *)

val validate_file_metat_data: file_meta_data -> int64 -> list (list (option offset_index))
  -> Tot bool

let validate_file_metat_data fmd footer_start group_offset_indices =
  if List.length group_offset_indices = List.length fmd.row_groups
  then
    List.Tot.for_all (fun (rg, offset_indices) ->
          if List.length offset_indices = List.length rg.columns
          then validate_row_group rg footer_start offset_indices
          else false)
      (zip fmd.row_groups group_offset_indices)
  else false
