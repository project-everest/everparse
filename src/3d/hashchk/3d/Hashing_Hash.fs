#light "off"
module Hashing_Hash
open Prims
open FStar_Pervasives
type c_files =
{wrapper_h : Prims.string FStar_Pervasives_Native.option; wrapper_c : Prims.string FStar_Pervasives_Native.option; h : Prims.string; c : Prims.string; assertions : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkc_files__item__wrapper_h : c_files  ->  Prims.string FStar_Pervasives_Native.option = (fun ( projectee  :  c_files ) -> (match (projectee) with
| {wrapper_h = wrapper_h; wrapper_c = wrapper_c; h = h; c = c; assertions = assertions} -> begin
wrapper_h
end))


let __proj__Mkc_files__item__wrapper_c : c_files  ->  Prims.string FStar_Pervasives_Native.option = (fun ( projectee  :  c_files ) -> (match (projectee) with
| {wrapper_h = wrapper_h; wrapper_c = wrapper_c; h = h; c = c; assertions = assertions} -> begin
wrapper_c
end))


let __proj__Mkc_files__item__h : c_files  ->  Prims.string = (fun ( projectee  :  c_files ) -> (match (projectee) with
| {wrapper_h = wrapper_h; wrapper_c = wrapper_c; h = h; c = c; assertions = assertions} -> begin
h
end))


let __proj__Mkc_files__item__c : c_files  ->  Prims.string = (fun ( projectee  :  c_files ) -> (match (projectee) with
| {wrapper_h = wrapper_h; wrapper_c = wrapper_c; h = h; c = c; assertions = assertions} -> begin
c
end))


let __proj__Mkc_files__item__assertions : c_files  ->  Prims.string FStar_Pervasives_Native.option = (fun ( projectee  :  c_files ) -> (match (projectee) with
| {wrapper_h = wrapper_h; wrapper_c = wrapper_c; h = h; c = c; assertions = assertions} -> begin
assertions
end))


let hash : Prims.string  ->  c_files FStar_Pervasives_Native.option  ->  Prims.string = (fun ( f  :  Prims.string ) ( opt_c  :  c_files FStar_Pervasives_Native.option ) -> (

let h = (Hashing_Op.hash_init ())
in ((Hashing_Op.hash_string h Version.everparse_version);
(Hashing_Op.hash_string h Version.fstar_commit);
(Hashing_Op.hash_string h Version.karamel_commit);
(Hashing_Op.hash_file h f);
(match (opt_c) with
| FStar_Pervasives_Native.None -> begin
(Hashing_Op.hash_bool h false)
end
| FStar_Pervasives_Native.Some (c) -> begin
((Hashing_Op.hash_bool h true);
(Hashing_Op.hash_file_option h c.wrapper_h);
(Hashing_Op.hash_file_option h c.wrapper_c);
(Hashing_Op.hash_file h c.h);
(Hashing_Op.hash_file h c.c);
(match (c.assertions) with
| FStar_Pervasives_Native.None -> begin
(Hashing_Op.hash_bool h false)
end
| FStar_Pervasives_Native.Some (assertions) -> begin
((Hashing_Op.hash_bool h true);
(Hashing_Op.hash_file h assertions);
)
end);
)
end);
(Hashing_Op.hash_finish h);
)))


let c_comment_intro : Prims.string = "EverParse checksum hash"


let hash_as_comment : Prims.string  ->  Prims.string = (fun ( file  :  Prims.string ) -> (

let h = (hash file FStar_Pervasives_Native.None)
in (Prims.strcat c_comment_intro (Prims.strcat ":" h))))

type check_inplace_hashes_t =
| AllHashes of c_files
| OneHash of Prims.string


let uu___is_AllHashes : check_inplace_hashes_t  ->  Prims.bool = (fun ( projectee  :  check_inplace_hashes_t ) -> (match (projectee) with
| AllHashes (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__AllHashes__item___0 : check_inplace_hashes_t  ->  c_files = (fun ( projectee  :  check_inplace_hashes_t ) -> (match (projectee) with
| AllHashes (_0) -> begin
_0
end))


let uu___is_OneHash : check_inplace_hashes_t  ->  Prims.bool = (fun ( projectee  :  check_inplace_hashes_t ) -> (match (projectee) with
| OneHash (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__OneHash__item___0 : check_inplace_hashes_t  ->  Prims.string = (fun ( projectee  :  check_inplace_hashes_t ) -> (match (projectee) with
| OneHash (_0) -> begin
_0
end))


let check_inplace_hashes_on : (Prims.string  ->  Prims.string  ->  Prims.bool)  ->  Prims.string  ->  check_inplace_hashes_t  ->  Prims.bool = (fun ( f  :  Prims.string  ->  Prims.string  ->  Prims.bool ) ( file_3d  :  Prims.string ) ( files_c  :  check_inplace_hashes_t ) -> (

let h = (hash file_3d FStar_Pervasives_Native.None)
in (match (files_c) with
| OneHash (c_file) -> begin
(f h c_file)
end
| AllHashes (files_c1) -> begin
(FStar_List.for_all (f h) (FStar_List_Tot_Base.append ((files_c1.c)::(files_c1.h)::(match (files_c1.wrapper_c) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (w) -> begin
(w)::[]
end)) (FStar_List_Tot_Base.append (match (files_c1.wrapper_h) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (w) -> begin
(w)::[]
end) (match (files_c1.assertions) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (assertions) -> begin
(assertions)::[]
end))))
end)))


let check_inplace_hash : (Prims.string  ->  Prims.string  ->  Prims.bool)  ->  Prims.string  ->  unit = (fun ( f  :  Prims.string  ->  Prims.string  ->  Prims.bool ) ( file_3d_file_c  :  Prims.string ) -> (

let eqstr' = (fun ( uu___  :  unit ) -> "=")
in (

let eqstr = (eqstr' ())
in (match ((FStar_String.split (((FStar_String.index eqstr (Prims.parse_int "0")))::[]) file_3d_file_c)) with
| (file_3d)::(file_c)::[] -> begin
(

let uu___ = (check_inplace_hashes_on f file_3d (OneHash (file_c)))
in (match (uu___) with
| true -> begin
(FStar_IO.print_string (Prims.strcat "EverParse check_inplace_hash succeeded on " (Prims.strcat file_3d "\n")))
end
| uu___1 -> begin
((FStar_IO.print_string (Prims.strcat "EverParse check_inplace_hash failed on " (Prims.strcat file_3d "\n")));
(FStar_All.exit (Prims.parse_int "255"));
)
end))
end
| uu___ -> begin
(failwith "check_inplace_hash: expected file.3d=file.h")
end))))


let check_inplace_hashes : (Prims.string  ->  Prims.string  ->  Prims.bool)  ->  Prims.string Prims.list  ->  unit = (fun ( f  :  Prims.string  ->  Prims.string  ->  Prims.bool ) -> (FStar_List.iter (check_inplace_hash f)))




