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
   file_meta_data                                                            
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

(*----------------------------------------------------------------------
   offset_index                                                            
  --------------------------------------------------------------------*)
let convert_page_location (pl : pageLocation) : page_location =
  { offset = pl#grab_offset ;
    compressed_page_size1 = pl#grab_compressed_page_size ;
    first_row_index = pl#grab_first_row_index ;
  }

let convert_offset_index (oi : offsetIndex) : offset_index =
  { page_locations = List.map convert_page_location (oi#grab_page_locations) ;
    unencoded_byte_array_data_bytes1 = oi#get_unencoded_byte_array_data_bytes ;
  }

(*----------------------------------------------------------------------
   pretty printer                                                            
  --------------------------------------------------------------------*)
open Format
(* generic helpers --------------------------------------------------- *)
let pp_string fmt s = fprintf fmt "%S" s

(* let list_sep fmt () = pp_print_string fmt "; "      (* “; ” with break *) *)
let list_sep = pp_print_cut
let pp_list pp_elt fmt lst =
  fprintf fmt "[@[%a@]]" (pp_print_list ~pp_sep:list_sep pp_elt) lst

let pp_opt pp fmt = function
  | None   -> pp_print_string fmt "None"
  | Some x -> fprintf fmt "Some(@[<v>%a@])" pp x
let pp_i32 fmt i = pp_print_string fmt (FStar_Int32.to_string i)

let pp_i64 fmt i = pp_print_string fmt (FStar_Int64.to_string i)
let pp_i16 fmt i = pp_print_string fmt (FStar_Int16.to_string i)
let pp_i8  fmt i = pp_print_string fmt (FStar_Int8.to_string  i)

(* enum printers ----------------------------------------------------- *)
let pp_physical_type fmt = function
  | BOOLEAN            -> pp_print_string fmt "BOOLEAN"
  | INT32              -> pp_print_string fmt "INT32"
  | INT64              -> pp_print_string fmt "INT64"
  | INT96              -> pp_print_string fmt "INT96"
  | FLOAT              -> pp_print_string fmt "FLOAT"
  | DOUBLE             -> pp_print_string fmt "DOUBLE"
  | BYTE_ARRAY         -> pp_print_string fmt "BYTE_ARRAY"
  | FIXED_LEN_BYTE_ARRAY -> pp_print_string fmt "FIXED_LEN_BYTE_ARRAY"

let pp_repetition fmt = function
  | REQUIRED -> pp_print_string fmt "REQUIRED"
  | OPTIONAL -> pp_print_string fmt "OPTIONAL"
  | REPEATED -> pp_print_string fmt "REPEATED"

let pp_encoding fmt = function
  | PLAIN                   -> pp_print_string fmt "PLAIN"
  | PLAIN_DICTIONARY        -> pp_print_string fmt "PLAIN_DICTIONARY"
  | RLE                     -> pp_print_string fmt "RLE"
  | BIT_PACKED              -> pp_print_string fmt "BIT_PACKED"
  | DELTA_BINARY_PACKED     -> pp_print_string fmt "DELTA_BINARY_PACKED"
  | DELTA_LENGTH_BYTE_ARRAY -> pp_print_string fmt "DELTA_LENGTH_BYTE_ARRAY"
  | DELTA_BYTE_ARRAY        -> pp_print_string fmt "DELTA_BYTE_ARRAY"
  | RLE_DICTIONARY          -> pp_print_string fmt "RLE_DICTIONARY"
  | BYTE_STREAM_SPLIT       -> pp_print_string fmt "BYTE_STREAM_SPLIT"

let pp_codec fmt = function
  | UNCOMPRESSED -> pp_print_string fmt "UNCOMPRESSED"
  | SNAPPY       -> pp_print_string fmt "SNAPPY"
  | GZIP         -> pp_print_string fmt "GZIP"
  | LZO          -> pp_print_string fmt "LZO"
  | BROTLI       -> pp_print_string fmt "BROTLI"
  | LZ4          -> pp_print_string fmt "LZ4"
  | ZSTD         -> pp_print_string fmt "ZSTD"
  | LZ4_RAW      -> pp_print_string fmt "LZ4_RAW"

(* schema_element ---------------------------------------------------- *)
let pp_schema_element fmt se =
  fprintf fmt "@[<v2>{@,\
    @[<hov2>name = \"%s\";@]@,\
    @[<hov2>rep = %a;@]@,\
    @[<hov2>type = %a;@]@,\
    @[<hov2>num_children = %a@]@,\
  }@]"
    se.name
    (pp_opt pp_repetition) se.repetition_type
    (pp_opt pp_physical_type) se.type_
    (pp_opt pp_i32) se.num_children

let pp_path fmt p = pp_string fmt (String.concat "." p)

(* column_meta_data (trimmed to fields used by validator) ------------ *)
let pp_column_meta fmt cm =
  fprintf fmt
    "@[<v 2>{@,\
    path                 = %a;@,\
    codec                = %a;@,\
    values               = %a;@,\
    comp_size            = %a;@,\
    data_page_offset     = %a;@,\
    index_page_offset    = %a;@,\
    dictionary_page_offset = %a;@,\
    }@]"
    pp_path cm.path_in_schema
    pp_codec cm.codec
    pp_i64  cm.num_values3
    pp_i64  cm.total_compressed_size
    pp_i64  cm.data_page_offset
    (pp_opt pp_i64) cm.index_page_offset
    (pp_opt pp_i64) cm.dictionary_page_offset

(* column_chunk ------------------------------------------------------ *)
let pp_column_chunk fmt cc =
  fprintf fmt "@[<v 2>{@,\
  file_off = %a;@,\
  meta = %a;@,\
  offset_index_offset = %a;@,\
  offset_index_length = %a;@,\
  column_index_offset = %a;@,\
  column_index_length = %a@,\
}@]"
    pp_i64 cc.file_offset
    (pp_opt pp_column_meta) cc.meta_data
    (pp_opt pp_i64) cc.offset_index_offset
    (pp_opt pp_i32) cc.offset_index_length
    (pp_opt pp_i64) cc.column_index_offset
    (pp_opt pp_i32) cc.column_index_length

(* row_group --------------------------------------------------------- *)
let pp_row_group fmt rg =
  fprintf fmt "@[<v 2>{@,\
  rows                = %a;@,\
  total_sz            = %a;@,\
  columns             = %a;@,\
  file_offset         = %a;@,\
  total_compressed_sz = %a;@,\
  ordinal             = %a@,\
}@]"
    pp_i64 rg.num_rows1
    pp_i64 rg.total_byte_size
    (pp_list pp_column_chunk) rg.columns
    (pp_opt pp_i64) rg.file_offset1
    (pp_opt pp_i64) rg.total_compressed_size1
    (pp_opt pp_i16) rg.ordinal

(* file_meta_data --------------------------------------------------------- *)
let pp_file_meta_data fmt fmd =
  fprintf fmt "@[<v 2>{@,\
  version   = %a;@,\
  num_rows  = %a;@,\
  schema    = %a;@,\
  row_groups= %a@,\
  @]}@]"
    pp_i32   fmd.version
    pp_i64   fmd.num_rows2
    (pp_list pp_schema_element) fmd.schema
    (pp_list pp_row_group)      fmd.row_groups

(* page_location ----------------------------------------------------- *)
let pp_page_location fmt (pl: page_location) =
  fprintf fmt "@[<v 2>{@,\
  offset = %a;@,\
  compressed_page_size1 = %a;@,\
  first_row_index = %a;@,\
  }@]"
    pp_i64 pl.offset
    pp_i32 pl.compressed_page_size1
    pp_i64 pl.first_row_index

(* offset_index ------------------------------------------------------ *)
let pp_offset_index fmt (oi: offset_index) = 
  fprintf fmt "@[<v 2>{@,\
  page_locations = %a;@,\
  unencoded_byte_array_data_bytes1 = %a@,\
  }@]"
    (pp_list pp_page_location) oi.page_locations
    (pp_opt (pp_list pp_i64)) oi.unencoded_byte_array_data_bytes1


(* convenience string renderers ------------------------------------- *)
let show pp v = Format.asprintf "%a" pp v
let show_file_meta_data = show pp_file_meta_data
