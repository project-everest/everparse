module HashingOptions

type check_hashes_t = | WeakHashes | StrongHashes | InplaceHashes

let is_weak = function
  | WeakHashes
  | InplaceHashes -> true
  | _ -> false

type micro_step_t =
  | MicroStepVerify
  | MicroStepExtract
  | MicroStepCopyClangFormat
  | MicroStepCopyEverParseH
  | MicroStepEmitConfig
  
type makefile_type =
  | MakefileGMake
  | MakefileNMake

type input_stream_binding_t =
  | InputStreamBuffer
  | InputStreamExtern:
    (include_file: string) ->
    input_stream_binding_t
  | InputStreamStatic:
    (include_file: string) ->
    input_stream_binding_t

let string_of_input_stream_binding = function
  | InputStreamBuffer -> "buffer"
  | InputStreamExtern _ -> "extern"
  | InputStreamStatic _ -> "static"

let input_stream_include = function
  | InputStreamBuffer -> ""
  | InputStreamStatic s
  | InputStreamExtern s -> s
