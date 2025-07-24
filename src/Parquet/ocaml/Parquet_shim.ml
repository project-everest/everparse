(*--------------------------------------------------------------------
   Shim layer:  convert the *mutable* Thrift‑generated objects 
   *pure* F* records. Only the fields needed by the validator are mapped
   right now.
  -------------------------------------------------------------------*)

open Parquet_types               
include Parquet_Spec_Validator

(* Helpers -----------------------------------------------------------*)
let opt_map f = function None -> None | Some x -> Some (f x)
  

(*----------------------------------------------------------------------
  Enum conversions (one‑to‑one mapping)                                 
  --------------------------------------------------------------------*)
let conv_physical_type : Type.t -> physical_type = function
  | Type.BOOLEAN            -> BOOLEAN
  | INT32                   -> INT32
  | INT64                   -> INT64
  | INT96                   -> INT96
  | FLOAT                   -> FLOAT
  | DOUBLE                  -> DOUBLE
  | BYTE_ARRAY              -> BYTE_ARRAY
  | FIXED_LEN_BYTE_ARRAY    -> FIXED_LEN_BYTE_ARRAY

let conv_repetition_type : FieldRepetitionType.t -> field_repetition_type =
  function
  | REQUIRED  -> REQUIRED
  | OPTIONAL  -> OPTIONAL
  | REPEATED  -> REPEATED

let conv_encoding : Encoding.t -> encoding = function
  | PLAIN                   -> PLAIN
  | PLAIN_DICTIONARY        -> PLAIN_DICTIONARY
  | RLE                     -> RLE
  | BIT_PACKED              -> BIT_PACKED
  | DELTA_BINARY_PACKED     -> DELTA_BINARY_PACKED
  | DELTA_LENGTH_BYTE_ARRAY -> DELTA_LENGTH_BYTE_ARRAY
  | DELTA_BYTE_ARRAY        -> DELTA_BYTE_ARRAY
  | RLE_DICTIONARY          -> RLE_DICTIONARY
  | BYTE_STREAM_SPLIT       -> BYTE_STREAM_SPLIT

let conv_codec : CompressionCodec.t -> compression_codec = function
  | UNCOMPRESSED -> UNCOMPRESSED
  | SNAPPY       -> SNAPPY
  | GZIP         -> GZIP
  | LZO          -> LZO
  | BROTLI       -> BROTLI
  | LZ4          -> LZ4
  | ZSTD         -> ZSTD
  | LZ4_RAW      -> LZ4_RAW

(* ConvertedType, LogicalType, etc. omitted for now *)

(*----------------------------------------------------------------------
  Conversions                                                     
  --------------------------------------------------------------------*)
let rec convert_schema_element (se : schemaElement) : schema_element =
  { type_          = opt_map conv_physical_type (se#get_type) ;
    type_length    = (se#get_type_length) ;
    repetition_type= opt_map conv_repetition_type (se#get_repetition_type);
    name           = (try se#grab_name with _ -> "") ;
    num_children   = (se#get_num_children) ;
    converted_type = None ;
    scale1         = (se#get_scale) ;
    precision1     = (se#get_precision) ;
    field_id       = (se#get_field_id) ;
    logical_type   = None ;
  }

let convert_column_meta (cm : columnMetaData) : column_meta_data =
  { physical_type         = conv_physical_type (cm#grab_type) ;
    encodings             = List.map conv_encoding (cm#grab_encodings) ;
    path_in_schema        = cm#grab_path_in_schema ;
    codec                 = conv_codec (cm#grab_codec) ;
    num_values3           = (cm#grab_num_values) ;
    total_uncompressed_size = (cm#grab_total_uncompressed_size) ;
    total_compressed_size   = (cm#grab_total_compressed_size) ;
    key_value_metadata       = None ;
    data_page_offset         = (cm#grab_data_page_offset) ;
    index_page_offset        = (cm#get_index_page_offset) ;
    dictionary_page_offset   = (cm#get_dictionary_page_offset);
    statistics2              = None ;
    encoding_stats           = None ;
    bloom_filter_offset      = (cm#get_bloom_filter_offset) ;
    bloom_filter_length      = (cm#get_bloom_filter_length) ;
    size_statistics          = None ;
    geospatial_statistics    = None ;
  }

let convert_column_chunk (cc : columnChunk) : column_chunk =
  { file_path                  = cc#get_file_path ;
    file_offset                = (cc#grab_file_offset) ;
    meta_data                  = opt_map convert_column_meta (cc#get_meta_data) ;
    offset_index_offset        = (cc#get_offset_index_offset);
    offset_index_length        = (cc#get_offset_index_length);
    column_index_offset        = (cc#get_column_index_offset);
    column_index_length        = (cc#get_column_index_length);
    crypto_metadata            = None ;
    encrypted_column_metadata  = cc#get_encrypted_column_metadata ;
  }

let convert_row_group (rg : rowGroup) : row_group =
  { columns                = List.map convert_column_chunk (rg#grab_columns) ;
    total_byte_size        = (rg#grab_total_byte_size) ;
    num_rows1              = (rg#grab_num_rows) ;
    sorting_columns        = None ;
    file_offset1           = (rg#get_file_offset) ;
    total_compressed_size1 = (rg#get_total_compressed_size) ;
    ordinal                = opt_map FStar_Int16.of_native_int (rg#get_ordinal) ;
  }

(*----------------------------------------------------------------------
   Top‑level                                                            
  --------------------------------------------------------------------*)
let convert_file_meta_data (fm : fileMetaData) : file_meta_data =
  { version                     = (fm#grab_version) ;
    schema                      = List.map convert_schema_element (fm#grab_schema) ;
    num_rows2                   = (fm#grab_num_rows) ;
    row_groups                  = List.map convert_row_group (fm#grab_row_groups) ;
    key_value_metadata1         = None ;
    created_by                  = fm#get_created_by ;
    column_orders               = None ;
    encryption_algorithm        = None ;
    footer_signing_key_metadata = fm#get_footer_signing_key_metadata ;
  }
