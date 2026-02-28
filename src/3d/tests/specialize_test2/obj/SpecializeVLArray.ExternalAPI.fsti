module SpecializeVLArray.ExternalAPI

open EverParse3d.Prelude
open EverParse3d.Actions.All
open EverParse3d.Interpreter
noextract
val output_loc:eloc


val ___ProbeAndCopy:EverParse3d.ProbeActions.probe_fn_incremental


val ___ProbeAndReadU32:EverParse3d.ProbeActions.probe_and_read_at_offset_uint32


val ___WriteU64:EverParse3d.ProbeActions.write_at_offset_uint64


val ___ProbeInit:EverParse3d.ProbeActions.init_probe_dest_t


val ___UlongToPtr (ptr: (___UINT32)) : EverParse3d.ProbeActions.pure_external_action (___UINT64)

