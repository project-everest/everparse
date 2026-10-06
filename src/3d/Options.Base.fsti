module Options.Base
open HashingOptions
open FStar.All

val module_name (file: string) : ML string

val get_api : unit -> ML api_t

val display_usage : unit -> ML unit

val compute_options (ignore: list string) : ML string

val parse_cmd_line : unit -> ML (list string)

val output_dir : unit -> ML string

val check_hashes : unit -> ML (option check_hashes_t)

val check_inplace_hashes : unit -> ML (list string)
