#light "off"
module Utils

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


let string_starts_with : Prims.string  ->  Prims.string  ->  Prims.bool = (fun ( big  :  Prims.string ) ( small  :  Prims.string ) -> (

let small_len = (FStar_String.strlen small)
in (match (((FStar_String.strlen big) < small_len)) with
| true -> begin
false
end
| uu___ -> begin
(Prims.op_Equality (FStar_String.sub big (Prims.parse_int "0") small_len) small)
end)))




