module Parquet.Pulse.Rel
#lang-pulse
open Pulse.Lib.Pervasives
module Rel = CDDL.Pulse.Types.Base
module V = Pulse.Lib.Vec
module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

module PV = Parquet.Pulse.Vec
module PS = Parquet.Spec.Toplevel
module PP = Parquet.Pulse.Toplevel

let rel = Rel.rel
let rel_opt = Rel.rel_option
[@@pulse_unfold]
let rel_vec_of_list = PV.rel_vec_of_list
[@@pulse_unfold]
let mk_rel = Rel.mk_rel


let rel_vec_of_seq
  (#t: Type)
: rel (PV.vec t) (Seq.seq t)
= mk_rel (fun (x: PV.vec t) y -> (x.data |-> y) ** pure (V.is_full_vec x.data /\ V.length x.data == SZ.v x.len))

let rel_byte : rel PP.byte PS.byte = Rel.rel_pure _
let rel_bytes : rel PP.bytes PS.bytes = rel_vec_of_seq

let rel_bool    : rel bool bool = Rel.rel_pure _
let rel_int8    : rel PP.int8 PS.int8 = Rel.rel_pure _
let rel_int16   : rel PP.int16 PS.int16 = Rel.rel_pure _
let rel_int32   : rel PP.int32 PS.int32 = Rel.rel_pure _
let rel_int64   : rel PP.int64 PS.int64 = Rel.rel_pure _
let rel_string  : rel string string = Rel.rel_pure _

// Enums
let rel_physical_type          : rel PP.physical_type PS.physical_type = Rel.rel_pure _
let rel_converted_type         : rel PP.converted_type PS.converted_type = Rel.rel_pure _
let rel_field_repetition_type  : rel PP.field_repetition_type PS.field_repetition_type = Rel.rel_pure _
let rel_encoding               : rel PP.encoding PS.encoding = Rel.rel_pure _
let rel_compression_codec      : rel PP.compression_codec PS.compression_codec = Rel.rel_pure _
let rel_page_type              : rel PP.page_type PS.page_type = Rel.rel_pure _
let rel_boundary_order         : rel PP.boundary_order PS.boundary_order = Rel.rel_pure _
let rel_edge_interp_alg        : rel PP.edge_interpolation_algorithm PS.edge_interpolation_algorithm = Rel.rel_pure _
let rel_time_unit              : rel PP.time_unit PS.time_unit = Rel.rel_pure _
let rel_logical_type           : rel PP.logical_type PS.logical_type = Rel.rel_pure _

let rel_bounding_box           : rel PP.bounding_box PS.bounding_box = Rel.rel_pure _
let rel_string_type            : rel PP.string_type PS.string_type   = Rel.rel_pure _
let rel_uuid_type              : rel PP.uuid_type   PS.uuid_type     = Rel.rel_pure _
let rel_key_value : rel PP.key_value PS.key_value = Rel.rel_pure _
// ... 


// sorting_column { column_idx:int32; descending:bool; nulls_first:bool }
let rel_sorting_column : rel PP.sorting_column PS.sorting_column = Rel.rel_pure _

// page_encoding_stats { page_type; encoding; count }
let rel_page_encoding_stats : rel PP.page_encoding_stats PS.page_encoding_stats = Rel.rel_pure _

// size_statistics: only vec<->list conversions
let rel_size_statistics : rel PP.size_statistics PS.size_statistics =
  mk_rel (fun (x: PP.size_statistics) (y: PS.size_statistics) ->
    rel_opt rel_int64 x.unencoded_byte_array_data_bytes y.unencoded_byte_array_data_bytes **
    rel_opt (rel_vec_of_list rel_int64) x.repetition_level_histogram y.repetition_level_histogram **
    rel_opt (rel_vec_of_list rel_int64) x.definition_level_histogram y.definition_level_histogram
  )

let rel_geospatial_statistics : rel PP.geospatial_statistics PS.geospatial_statistics =
  mk_rel (fun (x: PP.geospatial_statistics) (y: PS.geospatial_statistics) ->
    rel_opt rel_bounding_box x.bbox y.bbox **
    rel_opt (rel_vec_of_list rel_int32) x.geospatial_types y.geospatial_types
  )

let rel_statistics : rel PP.statistics PS.statistics =
  mk_rel (fun (x: PP.statistics) (y: PS.statistics) ->
    rel_opt rel_bytes x.max y.max **
    rel_opt rel_bytes x.min y.min **
    rel_opt rel_int64 x.null_count y.null_count **
    rel_opt rel_int64 x.distinct_count y.distinct_count **
    rel_opt rel_bytes x.max_value y.max_value **
    rel_opt rel_bytes x.min_value y.min_value **
    rel_opt rel_bool  x.is_max_value_exact y.is_max_value_exact **
    rel_opt rel_bool  x.is_min_value_exact y.is_min_value_exact
  )

let rel_data_page_header : rel PP.data_page_header PS.data_page_header =
  mk_rel (fun (x: PP.data_page_header) (y: PS.data_page_header) ->
    rel_int32 x.num_values y.num_values **
    rel_encoding x.encoding_ y.encoding_ **
    rel_encoding x.definition_level_encoding y.definition_level_encoding **
    rel_encoding x.repetition_level_encoding y.repetition_level_encoding **
    rel_opt rel_statistics x.statistics y.statistics
  )

let rel_index_page_header : rel PP.index_page_header PS.index_page_header = Rel.rel_unit

let rel_dictionary_page_header : rel PP.dictionary_page_header PS.dictionary_page_header =
  mk_rel (fun (x: PP.dictionary_page_header) (y: PS.dictionary_page_header) ->
    rel_int32 x.num_values y.num_values **
    rel_encoding x.encoding y.encoding **
    rel_opt rel_bool x.is_sorted y.is_sorted
  )

let rel_data_page_header_v2 : rel PP.data_page_header_v2 PS.data_page_header_v2 =
  mk_rel (fun (x: PP.data_page_header_v2) (y: PS.data_page_header_v2) ->
    rel_int32 x.num_values y.num_values **
    rel_int32 x.num_nulls y.num_nulls **
    rel_int32 x.num_rows y.num_rows **
    rel_encoding x.encoding y.encoding **
    rel_int32 x.definition_levels_byte_length y.definition_levels_byte_length **
    rel_int32 x.repetition_levels_byte_length y.repetition_levels_byte_length **
    rel_opt rel_bool x.is_compressed y.is_compressed **
    rel_opt rel_statistics x.statistics y.statistics
  )

let rel_page_header : rel PP.page_header PS.page_header =
  mk_rel (fun (x: PP.page_header) (y: PS.page_header) ->
    rel_page_type x.ptype y.ptype **
    rel_int32 x.uncompressed_page_size y.uncompressed_page_size **
    rel_int32 x.compressed_page_size y.compressed_page_size **
    rel_opt rel_int32 x.crc y.crc **
    rel_opt rel_data_page_header x.data_page_header y.data_page_header **
    rel_opt rel_index_page_header x.index_page_header y.index_page_header **
    rel_opt rel_dictionary_page_header x.dictionary_page_header y.dictionary_page_header **
    rel_opt rel_data_page_header_v2 x.data_page_header_v2 y.data_page_header_v2
  )

let rel_column_meta_data : rel PP.column_meta_data PS.column_meta_data =
  mk_rel (fun (x: PP.column_meta_data) (y: PS.column_meta_data) ->
    rel_physical_type x.physical_type y.physical_type **
    rel_vec_of_list rel_encoding x.encodings y.encodings **
    rel_vec_of_list rel_string  x.path_in_schema y.path_in_schema **
    rel_compression_codec x.codec y.codec **
    rel_int64 x.num_values y.num_values **
    rel_int64 x.total_uncompressed_size y.total_uncompressed_size **
    rel_int64 x.total_compressed_size y.total_compressed_size **
    rel_opt (rel_vec_of_list rel_key_value) x.key_value_metadata y.key_value_metadata **
    rel_int64 x.data_page_offset y.data_page_offset **
    rel_opt rel_int64 x.index_page_offset y.index_page_offset **
    rel_opt rel_int64 x.dictionary_page_offset y.dictionary_page_offset **
    rel_opt rel_statistics x.statistics y.statistics **
    rel_opt (rel_vec_of_list rel_page_encoding_stats) x.encoding_stats y.encoding_stats **
    rel_opt rel_int64 x.bloom_filter_offset y.bloom_filter_offset **
    rel_opt rel_int32 x.bloom_filter_length y.bloom_filter_length **
    rel_opt rel_size_statistics x.size_statistics y.size_statistics **
    rel_opt rel_geospatial_statistics x.geospatial_statistics y.geospatial_statistics
  )

let rel_encryption_with_footer_key
  : rel PP.encryption_with_footer_key PS.encryption_with_footer_key
= Rel.rel_unit

let rel_encryption_with_column_key : rel PP.encryption_with_column_key PS.encryption_with_column_key =
  mk_rel (fun (x: PP.encryption_with_column_key) (y: PS.encryption_with_column_key) ->
    rel_vec_of_list rel_string x.path_in_schema y.path_in_schema **
    rel_opt rel_string x.key_metadata y.key_metadata
  )

let rel_column_crypto_meta_data : rel PP.column_crypto_meta_data PS.column_crypto_meta_data =
  mk_rel (fun xl yl ->
    match xl, yl with
    | PP.ENCRYPTION_WITH_FOOTER_KEY xf, PS.ENCRYPTION_WITH_FOOTER_KEY yf ->
        rel_encryption_with_footer_key xf yf
    | PP.ENCRYPTION_WITH_COLUMN_KEY xc, PS.ENCRYPTION_WITH_COLUMN_KEY yc ->
        rel_encryption_with_column_key xc yc
    | _, _ -> pure False
  )

let rel_column_chunk : rel PP.column_chunk PS.column_chunk =
  mk_rel (fun (x: PP.column_chunk) (y: PS.column_chunk) ->
    rel_opt rel_string x.file_path y.file_path **
    rel_int64 x.file_offset y.file_offset **
    rel_opt rel_column_meta_data x.meta_data y.meta_data **
    rel_opt rel_int64 x.offset_index_offset y.offset_index_offset **
    rel_opt rel_int32 x.offset_index_length y.offset_index_length **
    rel_opt rel_int64 x.column_index_offset y.column_index_offset **
    rel_opt rel_int32 x.column_index_length y.column_index_length **
    rel_opt rel_column_crypto_meta_data x.crypto_metadata y.crypto_metadata **
    rel_opt rel_string x.encrypted_column_metadata y.encrypted_column_metadata
  )

let rel_row_group : rel PP.row_group PS.row_group =
  mk_rel (fun (x: PP.row_group) (y: PS.row_group) ->
    rel_vec_of_list rel_column_chunk x.columns y.columns **
    rel_int64 x.total_byte_size y.total_byte_size **
    rel_int64 x.num_rows y.num_rows **
    rel_opt (rel_vec_of_list rel_sorting_column) x.sorting_columns y.sorting_columns **
    rel_opt rel_int64 x.file_offset y.file_offset **
    rel_opt rel_int64 x.total_compressed_size y.total_compressed_size **
    rel_opt rel_int16 x.ordinal y.ordinal
  )

let rel_page_location : rel PP.page_location PS.page_location = Rel.rel_pure _

let rel_offset_index : rel PP.offset_index PS.offset_index =
  mk_rel (fun (x: PP.offset_index) (y: PS.offset_index) ->
    rel_vec_of_list rel_page_location x.page_locations y.page_locations **
    rel_opt (rel_vec_of_list rel_int64) x.unencoded_byte_array_data_bytes y.unencoded_byte_array_data_bytes
  )

let rel_column_index : rel PP.column_index PS.column_index =
  mk_rel (fun (x: PP.column_index) (y: PS.column_index) ->
    rel_vec_of_list rel_bool   x.null_pages y.null_pages **
    rel_vec_of_list rel_string x.min_values y.min_values **
    rel_vec_of_list rel_string x.max_values y.max_values **
    rel_boundary_order x.boundary_order y.boundary_order **
    rel_opt (rel_vec_of_list rel_int64) x.null_counts y.null_counts **
    rel_opt (rel_vec_of_list rel_int64) x.repetition_level_histograms y.repetition_level_histograms **
    rel_opt (rel_vec_of_list rel_int64) x.definition_level_histograms y.definition_level_histograms
  )

let rel_aes_gcm_v1     : rel PP.aes_gcm_v1 PS.aes_gcm_v1         = Rel.rel_pure _
let rel_aes_gcm_ctr_v1 : rel PP.aes_gcm_ctr_v1 PS.aes_gcm_ctr_v1 = Rel.rel_pure _

let rel_encryption_algorithm : rel PP.encryption_algorithm PS.encryption_algorithm = Rel.rel_pure _

let rel_schema_element : rel PP.schema_element PS.schema_element = Rel.rel_pure _

let rel_column_order : rel PP.column_order PS.column_order = Rel.rel_pure _

let rel_file_meta_data : rel PP.file_meta_data PS.file_meta_data =
  mk_rel (fun (x: PP.file_meta_data) (y: PS.file_meta_data) ->
    rel_int32 x.version y.version **
    rel_vec_of_list rel_schema_element x.schema y.schema **
    rel_int64 x.num_rows y.num_rows **
    rel_vec_of_list rel_row_group x.row_groups y.row_groups **
    rel_opt (rel_vec_of_list rel_key_value) x.key_value_metadata y.key_value_metadata **
    rel_opt rel_string x.created_by y.created_by **
    rel_opt (rel_vec_of_list rel_column_order) x.column_orders y.column_orders **
    rel_opt rel_encryption_algorithm x.encryption_algorithm y.encryption_algorithm **
    rel_opt rel_string x.footer_signing_key_metadata y.footer_signing_key_metadata
  )
