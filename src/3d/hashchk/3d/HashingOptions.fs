#light "off"
module HashingOptions
open Prims
open FStar_Pervasives
type check_hashes_t =
| WeakHashes
| StrongHashes
| InplaceHashes


let uu___is_WeakHashes : check_hashes_t  ->  Prims.bool = (fun ( projectee  :  check_hashes_t ) -> (match (projectee) with
| WeakHashes -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_StrongHashes : check_hashes_t  ->  Prims.bool = (fun ( projectee  :  check_hashes_t ) -> (match (projectee) with
| StrongHashes -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_InplaceHashes : check_hashes_t  ->  Prims.bool = (fun ( projectee  :  check_hashes_t ) -> (match (projectee) with
| InplaceHashes -> begin
true
end
| uu___ -> begin
false
end))


let is_weak : check_hashes_t  ->  Prims.bool = (fun ( uu___  :  check_hashes_t ) -> (match (uu___) with
| WeakHashes -> begin
true
end
| InplaceHashes -> begin
true
end
| uu___1 -> begin
false
end))

type micro_step_t =
| MicroStepVerify
| MicroStepExtract
| MicroStepCopyClangFormat
| MicroStepCopyEverParseH
| MicroStepEmitConfig


let uu___is_MicroStepVerify : micro_step_t  ->  Prims.bool = (fun ( projectee  :  micro_step_t ) -> (match (projectee) with
| MicroStepVerify -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_MicroStepExtract : micro_step_t  ->  Prims.bool = (fun ( projectee  :  micro_step_t ) -> (match (projectee) with
| MicroStepExtract -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_MicroStepCopyClangFormat : micro_step_t  ->  Prims.bool = (fun ( projectee  :  micro_step_t ) -> (match (projectee) with
| MicroStepCopyClangFormat -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_MicroStepCopyEverParseH : micro_step_t  ->  Prims.bool = (fun ( projectee  :  micro_step_t ) -> (match (projectee) with
| MicroStepCopyEverParseH -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_MicroStepEmitConfig : micro_step_t  ->  Prims.bool = (fun ( projectee  :  micro_step_t ) -> (match (projectee) with
| MicroStepEmitConfig -> begin
true
end
| uu___ -> begin
false
end))

type makefile_type =
| MakefileGMake
| MakefileNMake


let uu___is_MakefileGMake : makefile_type  ->  Prims.bool = (fun ( projectee  :  makefile_type ) -> (match (projectee) with
| MakefileGMake -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_MakefileNMake : makefile_type  ->  Prims.bool = (fun ( projectee  :  makefile_type ) -> (match (projectee) with
| MakefileNMake -> begin
true
end
| uu___ -> begin
false
end))

type input_stream_binding_t =
| InputStreamBuffer
| InputStreamExtern of Prims.string
| InputStreamStatic of Prims.string


let uu___is_InputStreamBuffer : input_stream_binding_t  ->  Prims.bool = (fun ( projectee  :  input_stream_binding_t ) -> (match (projectee) with
| InputStreamBuffer -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_InputStreamExtern : input_stream_binding_t  ->  Prims.bool = (fun ( projectee  :  input_stream_binding_t ) -> (match (projectee) with
| InputStreamExtern (include_file) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__InputStreamExtern__item__include_file : input_stream_binding_t  ->  Prims.string = (fun ( projectee  :  input_stream_binding_t ) -> (match (projectee) with
| InputStreamExtern (include_file) -> begin
include_file
end))


let uu___is_InputStreamStatic : input_stream_binding_t  ->  Prims.bool = (fun ( projectee  :  input_stream_binding_t ) -> (match (projectee) with
| InputStreamStatic (include_file) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__InputStreamStatic__item__include_file : input_stream_binding_t  ->  Prims.string = (fun ( projectee  :  input_stream_binding_t ) -> (match (projectee) with
| InputStreamStatic (include_file) -> begin
include_file
end))


let string_of_input_stream_binding : input_stream_binding_t  ->  Prims.string = (fun ( uu___  :  input_stream_binding_t ) -> (match (uu___) with
| InputStreamBuffer -> begin
"buffer"
end
| InputStreamExtern (uu___1) -> begin
"extern"
end
| InputStreamStatic (uu___1) -> begin
"static"
end))


let input_stream_include : input_stream_binding_t  ->  Prims.string = (fun ( uu___  :  input_stream_binding_t ) -> (match (uu___) with
| InputStreamBuffer -> begin
""
end
| InputStreamStatic (s) -> begin
s
end
| InputStreamExtern (s) -> begin
s
end))




