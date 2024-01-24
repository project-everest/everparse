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




