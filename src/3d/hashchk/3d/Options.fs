#light "off"
module Options
open Prims
open FStar_Pervasives

type valid_string =
Prims.string


let always_valid : Prims.string  ->  Prims.bool = (fun ( uu___  :  Prims.string ) -> true)


let starts_with_capital : Prims.string  ->  Prims.bool = (fun ( s  :  Prims.string ) -> (((FStar_String.strlen s) >= (Prims.parse_int "1")) && (

let first = (FStar_String.sub s (Prims.parse_int "0") (Prims.parse_int "1"))
in (((FStar_String.compare first "A") >= (Prims.parse_int "0")) && ((FStar_String.compare first "Z") <= (Prims.parse_int "0"))))))


let ends_with : Prims.string  ->  Prims.string  ->  Prims.bool = (fun ( s  :  Prims.string ) ( suffix  :  Prims.string ) -> (

let l = (FStar_String.strlen s)
in (

let sl = (FStar_String.strlen suffix)
in (match (((sl > l) || (Prims.op_Equality sl (Prims.parse_int "0")))) with
| true -> begin
false
end
| uu___ -> begin
(

let suffix' = (FStar_String.sub s (l - sl) sl)
in (Prims.op_Equality suffix suffix'))
end))))


let check_config_file_name : Prims.string  ->  Prims.bool = (fun ( fn  :  Prims.string ) -> (

let fn1 = (OS.basename fn)
in ((starts_with_capital fn1) && (ends_with fn1 ".3d.config"))))


let strip_suffix : Prims.string  ->  Prims.string  ->  Prims.string = (fun ( fn  :  Prims.string ) ( sfx  :  Prims.string ) -> (FStar_String.sub fn (Prims.parse_int "0") ((FStar_String.strlen fn) - (FStar_String.strlen sfx))))


type vstring =
Prims.string


let _arg0 : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _add_include : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let _batch : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _clang_format : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _clang_format_executable : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _cleanup : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _config_file : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _debug : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _inplace_hashes : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let _input_file : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let _json : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _no_copy_everparse_h : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _output_dir : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _save_hashes : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _save_z3_transcript : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _skip_c_makefiles : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _skip_deps : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _skip_o_rules : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let valid_micro_step : Prims.string  ->  Prims.bool = (fun ( str  :  Prims.string ) -> (match (str) with
| "verify" -> begin
true
end
| "extract" -> begin
true
end
| "copy_clang_format" -> begin
true
end
| "copy_everparse_h" -> begin
true
end
| "emit_config" -> begin
true
end
| uu___ -> begin
false
end))


let _micro_step : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _produce_c_from_existing_krml : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let valid_makefile : Prims.string  ->  Prims.bool = (fun ( str  :  Prims.string ) -> (match (str) with
| "gmake" -> begin
true
end
| "nmake" -> begin
true
end
| uu___ -> begin
false
end))


let _makefile : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _makefile_name : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let valid_equate_types : Prims.string  ->  Prims.bool = (fun ( str  :  Prims.string ) -> (

let l = (FStar_String.split ((',')::[]) str)
in (match (l) with
| (m1)::(m2)::[] -> begin
true
end
| uu___ -> begin
false
end)))


let _equate_types_list : Prims.string Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let valid_check_hashes : Prims.string  ->  Prims.bool = (fun ( uu___  :  Prims.string ) -> (match (uu___) with
| "weak" -> begin
true
end
| "strong" -> begin
true
end
| "inplace" -> begin
true
end
| uu___1 -> begin
false
end))


let _check_hashes : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let valid_input_stream_binding : Prims.string  ->  Prims.bool = (fun ( uu___  :  Prims.string ) -> (match (uu___) with
| "buffer" -> begin
true
end
| "extern" -> begin
true
end
| "static" -> begin
true
end
| uu___1 -> begin
false
end))


let _input_stream_binding : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _input_stream_include : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _emit_output_types_defs : Prims.bool FStar_ST.ref = (FStar_ST.alloc true)


let _emit_smt_encoding : Prims.bool FStar_ST.ref = (FStar_ST.alloc false)


let _z3_diff_test : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _z3_test : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let valid_z3_test_mode : Prims.string  ->  Prims.bool = (fun ( uu___  :  Prims.string ) -> (match (uu___) with
| "pos" -> begin
true
end
| "neg" -> begin
true
end
| "all" -> begin
true
end
| uu___1 -> begin
false
end))


let _z3_test_mode : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _z3_witnesses : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _z3_executable : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _test_checker : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _z3_branch_depth : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)


let _z3_options : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_ST.alloc FStar_Pervasives_Native.None)

type cmd_option_kind =
| OptBool of Prims.bool FStar_ST.ref
| OptStringOption of Prims.string * (Prims.string  ->  Prims.bool) * Prims.string FStar_Pervasives_Native.option FStar_ST.ref
| OptList of Prims.string * (Prims.string  ->  Prims.bool) * Prims.string Prims.list FStar_ST.ref


let uu___is_OptBool : cmd_option_kind  ->  Prims.bool = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptBool (v) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__OptBool__item__v : cmd_option_kind  ->  Prims.bool FStar_ST.ref = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptBool (v) -> begin
v
end))


let uu___is_OptStringOption : cmd_option_kind  ->  Prims.bool = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptStringOption (arg_desc, valid, v) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__OptStringOption__item__arg_desc : cmd_option_kind  ->  Prims.string = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptStringOption (arg_desc, valid, v) -> begin
arg_desc
end))


let __proj__OptStringOption__item__valid : cmd_option_kind  ->  Prims.string  ->  Prims.bool = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptStringOption (arg_desc, valid, v) -> begin
valid
end))


let __proj__OptStringOption__item__v : cmd_option_kind  ->  Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptStringOption (arg_desc, valid, v) -> begin
v
end))


let uu___is_OptList : cmd_option_kind  ->  Prims.bool = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptList (arg_desc, valid, v) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__OptList__item__arg_desc : cmd_option_kind  ->  Prims.string = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptList (arg_desc, valid, v) -> begin
arg_desc
end))


let __proj__OptList__item__valid : cmd_option_kind  ->  Prims.string  ->  Prims.bool = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptList (arg_desc, valid, v) -> begin
valid
end))


let __proj__OptList__item__v : cmd_option_kind  ->  Prims.string Prims.list FStar_ST.ref = (fun ( projectee  :  cmd_option_kind ) -> (match (projectee) with
| OptList (arg_desc, valid, v) -> begin
v
end))


type fstar_opt =
(FStarGetopt.opt * Prims.string)

type cmd_option =
| CmdOption of Prims.string * cmd_option_kind * Prims.string * Prims.string Prims.list
| CmdFStarOption of fstar_opt


let uu___is_CmdOption : cmd_option  ->  Prims.bool = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdOption (name, kind, desc, implies) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__CmdOption__item__name : cmd_option  ->  Prims.string = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdOption (name, kind, desc, implies) -> begin
name
end))


let __proj__CmdOption__item__kind : cmd_option  ->  cmd_option_kind = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdOption (name, kind, desc, implies) -> begin
kind
end))


let __proj__CmdOption__item__desc : cmd_option  ->  Prims.string = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdOption (name, kind, desc, implies) -> begin
desc
end))


let __proj__CmdOption__item__implies : cmd_option  ->  Prims.string Prims.list = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdOption (name, kind, desc, implies) -> begin
implies
end))


let uu___is_CmdFStarOption : cmd_option  ->  Prims.bool = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdFStarOption (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__CmdFStarOption__item___0 : cmd_option  ->  fstar_opt = (fun ( projectee  :  cmd_option ) -> (match (projectee) with
| CmdFStarOption (_0) -> begin
_0
end))


let cmd_option_name : cmd_option  ->  Prims.string = (fun ( a  :  cmd_option ) -> (match (a) with
| CmdFStarOption ((uu___, name', uu___1), uu___2) -> begin
name'
end
| CmdOption (name', uu___, uu___1, uu___2) -> begin
name'
end))


let rec find_cmd_option : Prims.string  ->  cmd_option Prims.list  ->  cmd_option FStar_Pervasives_Native.option = (fun ( name  :  Prims.string ) ( l  :  cmd_option Prims.list ) -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (a)::q -> begin
(match ((Prims.op_Equality name (cmd_option_name a))) with
| true -> begin
FStar_Pervasives_Native.Some (a)
end
| uu___ -> begin
(find_cmd_option name q)
end)
end))


let cmd_option_description : cmd_option  ->  Prims.string = (fun ( a  :  cmd_option ) -> (match (a) with
| CmdOption (uu___, uu___1, desc, uu___2) -> begin
desc
end
| CmdFStarOption (uu___, desc) -> begin
desc
end))


let cmd_option_arg_desc : cmd_option  ->  Prims.string = (fun ( a  :  cmd_option ) -> (match (a) with
| CmdFStarOption ((uu___, uu___1, arg), uu___2) -> begin
(match (arg) with
| FStarGetopt.OneArg (uu___3, argdesc) -> begin
argdesc
end
| uu___3 -> begin
""
end)
end
| CmdOption (uu___, kind, uu___1, uu___2) -> begin
(match (kind) with
| OptStringOption (argdesc, uu___3, uu___4) -> begin
argdesc
end
| OptList (argdesc, uu___3, uu___4) -> begin
argdesc
end
| uu___3 -> begin
""
end)
end))


let set_implies : cmd_option Prims.list FStar_ST.ref  ->  Prims.string Prims.list  ->  unit = (fun ( options  :  cmd_option Prims.list FStar_ST.ref ) ( implies  :  Prims.string Prims.list ) -> (FStar_List.iter (fun ( name  :  Prims.string ) -> (

let uu___ = (

let uu___1 = (FStar_ST.op_Bang options)
in (find_cmd_option name uu___1))
in (match (uu___) with
| FStar_Pervasives_Native.Some (CmdOption (uu___1, OptBool (x), uu___2, uu___3)) -> begin
(FStar_ST.op_Colon_Equals x true)
end
| uu___1 -> begin
()
end))) implies))


let string_starts_with : Prims.string  ->  Prims.string  ->  Prims.bool = (fun ( big  :  Prims.string ) ( small  :  Prims.string ) -> (

let small_len = (FStar_String.strlen small)
in (match (((FStar_String.strlen big) < small_len)) with
| true -> begin
false
end
| uu___ -> begin
(Prims.op_Equality (FStar_String.sub big (Prims.parse_int "0") small_len) small)
end)))


let negate_string_gen : Prims.string  ->  Prims.string  ->  Prims.string = (fun ( s  :  Prims.string ) ( negation  :  Prims.string ) -> (match ((string_starts_with s negation)) with
| true -> begin
(FStar_String.sub s (FStar_String.strlen negation) ((FStar_String.strlen s) - (FStar_String.strlen negation)))
end
| uu___ -> begin
(Prims.strcat negation s)
end))


let name_is_negated : Prims.string  ->  Prims.bool = (fun ( s  :  Prims.string ) -> (string_starts_with s "no_"))


let negate_name : Prims.string  ->  Prims.string = (fun ( s  :  Prims.string ) -> (negate_string_gen s "no_"))


let negate_description : Prims.string  ->  Prims.string = (fun ( s  :  Prims.string ) -> (negate_string_gen s "Do not"))


let fstar_options_of_cmd_option : cmd_option Prims.list FStar_ST.ref  ->  cmd_option  ->  fstar_opt Prims.list = (fun ( options  :  cmd_option Prims.list FStar_ST.ref ) ( o  :  cmd_option ) -> (match (o) with
| CmdFStarOption (f) -> begin
(f)::[]
end
| CmdOption (name, kind, desc, implies) -> begin
(match (kind) with
| OptBool (v) -> begin
(((((FStarGetopt.noshort), (name), (FStarGetopt.ZeroArgs ((fun ( uu___  :  unit ) -> ((set_implies options implies);
(FStar_ST.op_Colon_Equals v true);
)))))), (desc)))::(((((FStarGetopt.noshort), ((negate_name name)), (FStarGetopt.ZeroArgs ((fun ( uu___  :  unit ) -> (FStar_ST.op_Colon_Equals v false)))))), ((negate_description desc))))::[]
end
| OptStringOption (arg_desc, valid, v) -> begin
(((((FStarGetopt.noshort), (name), (FStarGetopt.OneArg ((((fun ( x  :  Prims.string ) -> (match ((valid x)) with
| true -> begin
((set_implies options implies);
(FStar_ST.op_Colon_Equals v (FStar_Pervasives_Native.Some (x)));
)
end
| uu___ -> begin
(failwith (Prims.strcat (Prims.strcat (Prims.strcat "Bad argument to " (Prims.strcat name ": got ")) (Prims.strcat x ", expected ")) (Prims.strcat arg_desc "")))
end))), (arg_desc)))))), (desc)))::(((((FStarGetopt.noshort), ((negate_name name)), (FStarGetopt.ZeroArgs ((fun ( uu___  :  unit ) -> (FStar_ST.op_Colon_Equals v FStar_Pervasives_Native.None)))))), ((negate_description desc))))::[]
end
| OptList (arg_desc, valid, v) -> begin
(((((FStarGetopt.noshort), (name), (FStarGetopt.OneArg ((((fun ( x  :  Prims.string ) -> (match ((valid x)) with
| true -> begin
((set_implies options implies);
(

let uu___1 = (

let uu___2 = (FStar_ST.op_Bang v)
in (x)::uu___2)
in (FStar_ST.op_Colon_Equals v uu___1));
)
end
| uu___ -> begin
(failwith (Prims.strcat (Prims.strcat (Prims.strcat "Bad argument to " (Prims.strcat name ": got ")) (Prims.strcat x ", expected ")) (Prims.strcat arg_desc "")))
end))), (arg_desc)))))), (desc)))::(((((FStarGetopt.noshort), ((negate_name name)), (FStarGetopt.ZeroArgs ((fun ( uu___  :  unit ) -> (FStar_ST.op_Colon_Equals v [])))))), (desc)))::[]
end)
end))


let compute_current_options : cmd_option Prims.list FStar_ST.ref  ->  Prims.string Prims.list  ->  Prims.string = (fun ( options  :  cmd_option Prims.list FStar_ST.ref ) ( ignore  :  Prims.string Prims.list ) -> (

let print = (fun ( msg  :  Prims.string ) ( opt  :  cmd_option ) -> (match ((FStar_List_Tot_Base.mem (cmd_option_name opt) ignore)) with
| true -> begin
msg
end
| uu___ -> begin
(match (opt) with
| CmdOption (name, kind, desc, implies) -> begin
(match (kind) with
| OptBool (v) -> begin
(

let uu___1 = (FStar_ST.op_Bang v)
in (match (uu___1) with
| true -> begin
(Prims.strcat (Prims.strcat "" (Prims.strcat msg " --")) (Prims.strcat name ""))
end
| uu___2 -> begin
msg
end))
end
| OptStringOption (uu___1, uu___2, v) -> begin
(

let uu___3 = (FStar_ST.op_Bang v)
in (match (uu___3) with
| FStar_Pervasives_Native.None -> begin
(Prims.strcat (Prims.strcat "" (Prims.strcat msg " --")) (Prims.strcat (negate_name name) ""))
end
| FStar_Pervasives_Native.Some (v1) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat "" (Prims.strcat msg " --")) (Prims.strcat name " ")) (Prims.strcat v1 ""))
end))
end
| OptList (uu___1, uu___2, v) -> begin
(

let v1 = (FStar_ST.op_Bang v)
in (

let msg1 = (Prims.strcat (Prims.strcat "" (Prims.strcat msg " --")) (Prims.strcat (negate_name name) ""))
in (

let app = (fun ( msg2  :  Prims.string ) ( s  :  Prims.string ) -> (Prims.strcat (Prims.strcat (Prims.strcat "" (Prims.strcat msg2 " --")) (Prims.strcat name " ")) (Prims.strcat s "")))
in (FStar_List_Tot_Base.fold_left app msg1 (FStar_List_Tot_Base.rev v1)))))
end)
end
| uu___1 -> begin
msg
end)
end))
in (

let msg = (

let uu___ = (FStar_ST.op_Bang options)
in (FStar_List.fold_left print "" uu___))
in (

let print_untoggle = (fun ( msg1  :  Prims.string ) ( opt  :  cmd_option ) -> (match (opt) with
| CmdOption (name, OptBool (v), uu___, uu___1) -> begin
(

let uu___2 = (match ((not ((FStar_List_Tot_Base.mem name ignore)))) with
| true -> begin
(

let uu___3 = (FStar_ST.op_Bang v)
in (not (uu___3)))
end
| uu___3 -> begin
false
end)
in (match (uu___2) with
| true -> begin
(Prims.strcat (Prims.strcat "" (Prims.strcat msg1 " --")) (Prims.strcat (negate_name name) ""))
end
| uu___3 -> begin
msg1
end))
end
| uu___ -> begin
msg1
end))
in (

let uu___ = (FStar_ST.op_Bang options)
in (FStar_List.fold_left print_untoggle msg uu___))))))


let arg0 : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _arg0)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
"3d"
end
| FStar_Pervasives_Native.Some (v) -> begin
v
end)))


let display_usage_1 : cmd_option Prims.list FStar_ST.ref  ->  unit = (fun ( options  :  cmd_option Prims.list FStar_ST.ref ) -> ((FStar_IO.print_string "EverParse/3d: verified data validation with dependent data descriptions\n");
(FStar_IO.print_string "\n");
(

let uu___3 = (

let uu___4 = (arg0 ())
in (Prims.strcat "Usage: " (Prims.strcat uu___4 " [options] path_to_input_file1.3d path_to_input_file2.3d ... \n")))
in (FStar_IO.print_string uu___3));
(FStar_IO.print_string "\n");
(FStar_IO.print_string "Options:\n");
(

let uu___6 = (FStar_ST.op_Bang options)
in (FStar_List.iter (fun ( x  :  cmd_option ) -> (

let m = (cmd_option_name x)
in (

let desc = (cmd_option_description x)
in (

let argdesc = (cmd_option_arg_desc x)
in (

let argdesc1 = (match ((Prims.op_Equality argdesc "")) with
| true -> begin
""
end
| uu___7 -> begin
(Prims.strcat " <" (Prims.strcat argdesc ">"))
end)
in (

let negate = (match ((uu___is_CmdOption x)) with
| true -> begin
(Prims.strcat " (opposite is --" (Prims.strcat (negate_name m) ")"))
end
| uu___7 -> begin
""
end)
in (

let visible = (not ((string_starts_with m "__")))
in (match (visible) with
| true -> begin
(FStar_IO.print_string (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "--" (Prims.strcat m "")) (Prims.strcat argdesc1 "")) (Prims.strcat negate "\n\t")) (Prims.strcat desc "\n")))
end
| uu___7 -> begin
()
end)))))))) uu___6));
(

let uu___6 = (

let uu___7 = (compute_current_options options [])
in (Prims.strcat "\nCurrent options are:" (Prims.strcat uu___7 "\n")))
in (FStar_IO.print_string uu___6));
))


let uu___256 : ((unit  ->  unit) * (Prims.string Prims.list  ->  Prims.string) * fstar_opt Prims.list) = (

let options = (FStar_ST.alloc [])
in (

let display_usage = (fun ( uu___  :  unit ) -> (display_usage_1 options))
in (

let compute_options = (compute_current_options options)
in ((FStar_ST.op_Colon_Equals options ((CmdOption ("add_include", OptList ("<include.h>|\"include.h\"", always_valid, _add_include), "Prepend #include ... to generated .c/.h files", []))::(CmdOption ("batch", OptBool (_batch), "Verify the generated F* code and extract C code", []))::(CmdOption ("check_hashes", OptStringOption ("weak|strong|inplace", valid_check_hashes, _check_hashes), "Check hashes", ("batch")::[]))::(CmdOption ("check_inplace_hash", OptList ("file.3d=file.h", always_valid, _inplace_hashes), "Check hashes stored in one .h/.c file", []))::(CmdOption ("clang_format", OptBool (_clang_format), "Call clang-format on extracted .c/.h files (--batch only)", ("batch")::[]))::(CmdOption ("clang_format_executable", OptStringOption ("clang-format full path", always_valid, _clang_format_executable), "Set the path to clang-format if not reachable through PATH", ("batch")::("clang_format")::[]))::(CmdOption ("cleanup", OptBool (_cleanup), "Remove *.fst*, *.krml and krml-args.rsp (--batch only)", []))::(CmdOption ("config", OptStringOption ("config file", check_config_file_name, _config_file), "The name of a JSON formatted file containing configuration options", []))::(CmdOption ("emit_output_types_defs", OptBool (_emit_output_types_defs), "Emit definitions of output types in a .h file", []))::(CmdOption ("emit_smt_encoding", OptBool (_emit_smt_encoding), "Emit an SMT encoding of parser specifications", []))::(CmdOption ("input_stream", OptStringOption ("buffer|extern|static", valid_input_stream_binding, _input_stream_binding), "Input stream binding (default buffer)", []))::(CmdOption ("input_stream_include", OptStringOption (".h file", always_valid, _input_stream_include), "Include file defining the EverParseInputStreamBase type (only for --input_stream extern or static)", []))::(CmdOption ("no_copy_everparse_h", OptBool (_no_copy_everparse_h), "Do not Copy EverParse.h (--batch only)", []))::(CmdOption ("debug", OptBool (_debug), "Emit a lot of debugging output", []))::(CmdFStarOption ((((('h'), ("help"), (FStarGetopt.ZeroArgs ((fun ( uu___1  :  unit ) -> ((display_usage ());
(FStar_All.exit (Prims.parse_int "0"));
)))))), ("Show this help message"))))::(CmdOption ("json", OptBool (_json), "Dump the AST in JSON format", []))::(CmdOption ("makefile", OptStringOption ("gmake|nmake", valid_makefile, _makefile), "Do not produce anything, other than a Makefile to produce everything", []))::(CmdOption ("makefile_name", OptStringOption ("some file name", always_valid, _makefile_name), "Name of the Makefile to produce (with --makefile, default <output directory>/EverParse.Makefile", []))::(CmdOption ("odir", OptStringOption ("output directory", always_valid, _output_dir), "output directory (default \'.\'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory", []))::(CmdOption ("save_hashes", OptBool (_save_hashes), "Save hashes", []))::(CmdOption ("save_z3_transcript", OptStringOption ("some file name", always_valid, _save_z3_transcript), "Save the Z3 transcript (input and output) to a file", []))::(CmdOption ("skip_c_makefiles", OptBool (_skip_c_makefiles), "Do not Generate Makefile.basic, Makefile.include", []))::(CmdOption ("skip_o_rules", OptBool (_skip_o_rules), "With --makefile, do not generate rules for .o files", []))::(CmdOption ("test_checker", OptStringOption ("parser name", always_valid, _test_checker), "produce a test checker executable", []))::(CmdFStarOption (((((FStarGetopt.noshort), ("version"), (FStarGetopt.ZeroArgs ((fun ( uu___1  :  unit ) -> ((FStar_IO.print_string (Prims.strcat "EverParse/3d " (Prims.strcat Version.everparse_version "\nCopyright 2018, 2019, 2020 Microsoft Corporation\n")));
(FStar_All.exit (Prims.parse_int "0"));
)))))), ("Show this version of EverParse"))))::(CmdOption ("equate_types", OptList ("an argument of the form A,B, to generate asserts of the form (A.t == B.t)", valid_equate_types, _equate_types_list), "Takes an argument of the form A,B and then for each entrypoint definition in B, it generates an assert (A.t == B.t) in the B.Types file, useful when refactoring specs, you can provide multiple equate_types on the command line", []))::(CmdOption ("z3_branch_depth", OptStringOption ("nb", always_valid, _z3_branch_depth), "enumerate branch choices up to depth nb (default 0)", []))::(CmdOption ("z3_diff_test", OptStringOption ("parser1,parser2", valid_equate_types, _z3_diff_test), "produce differential tests for two parsers", []))::(CmdOption ("z3_executable", OptStringOption ("path/to/z3", always_valid, _z3_executable), "z3 executable for test case generation (default `z3`; does not affect verification of generated F* code)", []))::(CmdOption ("z3_options", OptStringOption ("\'options to z3\'", always_valid, _z3_options), "command-line options to pass to z3 for test case generation (does not affect verification of generated F* code)", []))::(CmdOption ("z3_test", OptStringOption ("parser name", always_valid, _z3_test), "produce positive and/or negative test cases for a given parser", []))::(CmdOption ("z3_test_mode", OptStringOption ("pos|neg|all", valid_z3_test_mode, _z3_test_mode), "produce positive, negative, or all kinds of test cases (default all)", []))::(CmdOption ("z3_witnesses", OptStringOption ("nb", always_valid, _z3_witnesses), "ask for nb distinct test witnesses per branch case (default 1)", []))::(CmdOption ("__arg0", OptStringOption ("executable name", always_valid, _arg0), "executable name to use for the help message", []))::(CmdOption ("__micro_step", OptStringOption ("verify|extract|copy_clang_format|copy_everparse_h|emit_config", valid_micro_step, _micro_step), "micro step", []))::(CmdOption ("__produce_c_from_existing_krml", OptBool (_produce_c_from_existing_krml), "produce C from .krml files", []))::(CmdOption ("__skip_deps", OptBool (_skip_deps), "skip dependency analysis, assume all dependencies are specified on the command line", []))::[]));
(

let fstar_options = (

let uu___1 = (FStar_ST.op_Bang options)
in (FStar_List_Tot_Base.concatMap (fstar_options_of_cmd_option options) uu___1))
in ((display_usage), (compute_options), (fstar_options)));
))))


let display_usage_2 : unit  ->  unit = (match (uu___256) with
| (display_usage_21, compute_options_2, fstar_options) -> begin
display_usage_21
end)


let compute_options_2 : Prims.string Prims.list  ->  Prims.string = (match (uu___256) with
| (display_usage_21, compute_options_21, fstar_options) -> begin
compute_options_21
end)


let fstar_options : fstar_opt Prims.list = (match (uu___256) with
| (display_usage_21, compute_options_21, fstar_options1) -> begin
fstar_options1
end)


let display_usage : unit  ->  unit = display_usage_2


let compute_options : Prims.string Prims.list  ->  Prims.string = compute_options_2


let parse_cmd_line : unit  ->  Prims.string Prims.list = (fun ( uu___  :  unit ) -> (

let res = (FStarGetopt.parse_cmdline (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst fstar_options) (fun ( file  :  Prims.string ) -> ((

let uu___2 = (

let uu___3 = (FStar_ST.op_Bang _input_file)
in (file)::uu___3)
in (FStar_ST.op_Colon_Equals _input_file uu___2));
FStarGetopt.Success;
)))
in (match (res) with
| FStarGetopt.Success -> begin
(FStar_ST.op_Bang _input_file)
end
| FStarGetopt.Help -> begin
((display_usage ());
(FStar_All.exit (Prims.parse_int "0"));
)
end
| FStarGetopt.Error (s) -> begin
((FStar_IO.print_string s);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu___1 -> begin
(FStar_All.exit (Prims.parse_int "2"))
end)))


let split_3d_file_name : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun ( fn  :  Prims.string ) -> (

let fn1 = (OS.basename fn)
in (match ((Prims.op_Equality (OS.extension fn1) ".3d")) with
| true -> begin
FStar_Pervasives_Native.Some ((OS.remove_extension fn1))
end
| uu___ -> begin
FStar_Pervasives_Native.None
end)))


let file_name : Prims.string  ->  Prims.string = (fun ( mname  :  Prims.string ) -> (Prims.strcat mname ".3d"))


let module_name : Prims.string  ->  Prims.string = (fun ( file  :  Prims.string ) -> (match ((split_3d_file_name file)) with
| FStar_Pervasives_Native.Some (nm) -> begin
(match ((starts_with_capital nm)) with
| true -> begin
nm
end
| uu___ -> begin
(failwith (Prims.strcat "Input file name " (Prims.strcat file " must start with a capital letter")))
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Input file name " (Prims.strcat file " must end with .3d")))
end))


let output_dir : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _output_dir)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
"."
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let debug_print_string : Prims.string  ->  unit = (fun ( s  :  Prims.string ) -> (

let uu___ = (FStar_ST.op_Bang _debug)
in (match (uu___) with
| true -> begin
(FStar_IO.print_string s)
end
| uu___1 -> begin
()
end)))


let batch : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _batch))


let clang_format : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _clang_format))


let clang_format_executable : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _clang_format_executable)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let cleanup : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _cleanup))


let skip_c_makefiles : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _skip_c_makefiles))


let no_everparse_h : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _no_copy_everparse_h))


let check_hashes : unit  ->  HashingOptions.check_hashes_t FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _batch)
in (match (uu___1) with
| true -> begin
(

let uu___2 = (FStar_ST.op_Bang _check_hashes)
in (match (uu___2) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ("weak") -> begin
FStar_Pervasives_Native.Some (HashingOptions.WeakHashes)
end
| FStar_Pervasives_Native.Some ("strong") -> begin
FStar_Pervasives_Native.Some (HashingOptions.StrongHashes)
end
| FStar_Pervasives_Native.Some ("inplace") -> begin
FStar_Pervasives_Native.Some (HashingOptions.InplaceHashes)
end))
end
| uu___2 -> begin
FStar_Pervasives_Native.None
end)))


let save_hashes : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _save_hashes))


let check_inplace_hashes : unit  ->  Prims.string Prims.list = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _inplace_hashes)
in (FStar_List_Tot_Base.rev uu___1)))


let equate_types_list : unit  ->  (Prims.string * Prims.string) Prims.list = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _equate_types_list)
in (FStar_List.map (fun ( x  :  Prims.string ) -> (

let uu___2 = (FStar_String.split ((',')::[]) x)
in (match (uu___2) with
| (a)::(b)::[] -> begin
((a), (b))
end))) uu___1)))


let micro_step : unit  ->  HashingOptions.micro_step_t FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _micro_step)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ("verify") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MicroStepVerify)
end
| FStar_Pervasives_Native.Some ("extract") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MicroStepExtract)
end
| FStar_Pervasives_Native.Some ("copy_clang_format") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MicroStepCopyClangFormat)
end
| FStar_Pervasives_Native.Some ("copy_everparse_h") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MicroStepCopyEverParseH)
end
| FStar_Pervasives_Native.Some ("emit_config") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MicroStepEmitConfig)
end)))


let produce_c_from_existing_krml : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _produce_c_from_existing_krml))


let skip_deps : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _skip_deps))


let makefile : unit  ->  HashingOptions.makefile_type FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _makefile)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ("gmake") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MakefileGMake)
end
| FStar_Pervasives_Native.Some ("nmake") -> begin
FStar_Pervasives_Native.Some (HashingOptions.MakefileNMake)
end)))


let makefile_name : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _makefile_name)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
(

let uu___2 = (output_dir ())
in (OS.concat uu___2 "EverParse.Makefile"))
end
| FStar_Pervasives_Native.Some (mf) -> begin
mf
end)))


let skip_o_rules : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _skip_o_rules))


let json : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _json))


let input_stream_binding : unit  ->  HashingOptions.input_stream_binding_t = (fun ( uu___  :  unit ) -> (

let input_stream_include = (fun ( uu___1  :  unit ) -> (

let uu___2 = (FStar_ST.op_Bang _input_stream_include)
in (match (uu___2) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))
in (

let uu___1 = (FStar_ST.op_Bang _input_stream_binding)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
HashingOptions.InputStreamBuffer
end
| FStar_Pervasives_Native.Some ("buffer") -> begin
HashingOptions.InputStreamBuffer
end
| FStar_Pervasives_Native.Some ("extern") -> begin
(

let uu___2 = (input_stream_include ())
in HashingOptions.InputStreamExtern (uu___2))
end
| FStar_Pervasives_Native.Some ("static") -> begin
(

let uu___2 = (input_stream_include ())
in HashingOptions.InputStreamStatic (uu___2))
end))))


let emit_output_types_defs : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _emit_output_types_defs))


let config_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _config_file)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
FStar_Pervasives_Native.Some (s)
end)))


let add_include : unit  ->  Prims.string Prims.list = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _add_include))


let make_includes : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let incs = (add_include ())
in (FStar_List_Tot_Base.fold_left (fun ( accu  :  Prims.string ) ( inc  :  Prims.string ) -> (Prims.strcat (Prims.strcat "" (Prims.strcat accu "#include ")) (Prims.strcat inc "\n"))) "" incs)))


let config_module_name : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _config_file)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
FStar_Pervasives_Native.Some ((strip_suffix (OS.basename s) ".3d.config"))
end)))


let emit_smt_encoding : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _emit_smt_encoding))


let z3_test : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _z3_test))


let z3_pos_test : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_test)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
false
end
| uu___2 -> begin
(

let uu___3 = (FStar_ST.op_Bang _z3_test_mode)
in (match (uu___3) with
| FStar_Pervasives_Native.Some ("neg") -> begin
false
end
| uu___4 -> begin
true
end))
end)))


let z3_neg_test : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_test)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
false
end
| uu___2 -> begin
(

let uu___3 = (FStar_ST.op_Bang _z3_test_mode)
in (match (uu___3) with
| FStar_Pervasives_Native.Some ("pos") -> begin
false
end
| uu___4 -> begin
true
end))
end)))


let z3_witnesses : unit  ->  Prims.pos = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_witnesses)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
(Prims.parse_int "1")
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_All.try_with (fun ( uu___2  :  unit ) -> (match (()) with
| () -> begin
(

let n = (OS.int_of_string s)
in (match ((n < (Prims.parse_int "1"))) with
| true -> begin
(Prims.parse_int "1")
end
| uu___3 -> begin
n
end))
end)) (fun ( uu___2  :  Prims.exn ) -> (Prims.parse_int "1")))
end)))


let debug : unit  ->  Prims.bool = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _debug))


let z3_diff_test : unit  ->  (Prims.string * Prims.string) FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_diff_test)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
(

let uu___2 = (FStar_String.split ((',')::[]) s)
in (match (uu___2) with
| (p1)::(p2)::[] -> begin
FStar_Pervasives_Native.Some (((p1), (p2)))
end))
end)))


let z3_executable : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_executable)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
"z3"
end
| FStar_Pervasives_Native.Some (z3) -> begin
z3
end)))


let save_z3_transcript : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _save_z3_transcript))


let test_checker : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun ( uu___  :  unit ) -> (FStar_ST.op_Bang _test_checker))


let z3_branch_depth : unit  ->  Prims.nat = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_branch_depth)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
(Prims.parse_int "0")
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_All.try_with (fun ( uu___2  :  unit ) -> (match (()) with
| () -> begin
(

let n = (OS.int_of_string s)
in (match ((n < (Prims.parse_int "0"))) with
| true -> begin
(Prims.parse_int "0")
end
| uu___3 -> begin
n
end))
end)) (fun ( uu___2  :  Prims.exn ) -> (Prims.parse_int "0")))
end)))


let z3_options : unit  ->  Prims.string = (fun ( uu___  :  unit ) -> (

let uu___1 = (FStar_ST.op_Bang _z3_options)
in (match (uu___1) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))




