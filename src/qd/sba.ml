(*
	A simple array reindexer
	Avoids the many copies created by Array.sub
	(c) 2014 Microsoft Research
*)

open BatString

type bytes = {
	a : string;
	s : int;
	l : int;
}

let create (c:string) : bytes =
	{a=c; s=0; l=length c}

let is_empty (a:bytes) : bool =
	a.l = 0

let sub (sa:bytes) (start:int) (len:int) : bytes =
	let len = if len=0 then sa.l-start else len in
	if start < 0 || len < 0 || start + len > sa.l then failwith "OutOfBounds"
	else {sa with s=sa.s+start; l=len}

let get (sa:bytes) (off:int) =
	sa.a.[sa.s+off]

let set (sa:bytes) (off:int) (v:char) =
	sa.a.[sa.s+off] <- v

let peek (sa:bytes) (off:int) (l:int) =
	let l = if l=0 then sa.l else l in
	try
		BatString.sub sa.a (sa.s+off) l
		|> to_list
	with
	| _ -> failwith "OutOfBounds"

let b2ba (sa:bytes) : string =
	BatString.sub sa.a sa.s sa.l

let b2list (sa:bytes) : (char list) =
	b2ba sa
	|> BatString.to_list

let list2b (la:(char list)) : bytes =
	la |> BatString.of_list |> create

let beq (a:bytes) (b:bytes) : bool =
	b2list a = b2list b

let blen (sa:bytes) = sa.l

let rec trimz = function
	| '\000' :: t -> trimz t
	| l -> l    

let oid2b x =
	create x (*TODO*)

let b2oid x =
	let rec next = function
	| x::t ->
		let (u, b, v) = next t in
		let x = BatChar.code x in
		if x land 128 = 0 then
		  (x, 1, (if b>0 then "." ^ (string_of_int u)
				  else "") ^ v)
		else
		  (((x land 127) lsl (7*b)) + u, b + 1, v)
	| [] -> (0, 0, "") in
	match b2list x with
	| h::r ->
		let (u, b, v) = next r in
		let t = "." ^ (string_of_int u) ^ v in
		let hc = (BatChar.code h) in
		(string_of_int (hc/40)) ^ "." ^ (string_of_int (hc mod 40)) ^ t
	| _ -> failwith "Invalid OID"

(*TODO UTF8 *)
let str2b (x:string) =
	create x

let b2str (b:bytes) =
	b2ba b

let b2ascii (b:bytes) =
	b2ba b

let hex2b (s:string) =
	let c2hex c =
	  let c = BatChar.code c in
	  Printf.sprintf "%X" c in
	create (BatString.replace_chars c2hex s)

let b2hex (b:bytes) =
	let open Hex in
	let hex = of_string (b2ba b) in
	hexdump_s ~print_row_numbers:false ~print_chars:false hex

let int2b (s:string) =
	let base = BatString.init 256 char_of_int in
	let bx = BatBig_int.big_int_of_string s in
	let r = BatBig_int.to_string_in_custom_base base 256 bx in
	let pos = BatBig_int.sign_big_int bx >= 0 in
	if pos && (Pervasives.compare r.[0] '\128') >= 0 then
	  create ("\000" ^ r)
	else
	  create r

let b2int (b:bytes) =
	b2ba b

let bitstr2b (s:string) = 
	create s (*TODO*)
(*
	let mutable t = new String(s.ToCharArray() |> Array.rev)
	let mutable i = 0
	while t.Length % 8 <> 0 do t <- t+"0"; i <- i+1 done
	t
	|> Seq.windowed 8
	|> Seq.mapi (fun i j -> (i,j))
	|> Seq.filter (fun (i,j) -> i % 8 = 0)
	|> Seq.map (fun (_,j) -> Convert.ToByte(new String(j), 2))
	|> Array.ofSeq
	|> create
*)

let bitstrdec (x:bytes) =
	let ba = b2ba x in
	let zb = ba.[0] in
	let ba = String.sub ba 1 (String.length ba - 1) in
	ba
(* TODO
	let x = new BigInteger(Array.rev ba)
	BigInteger.op_RightShift(x, int zb).ToByteArray()
*)

let isIA5 (b:bytes) =
	let filtered = b2ba b
		|> filter (fun b -> Pervasives.compare b '\128' >= 0) in
	length filtered = 0

let isTeletex (b:bytes) =
	let filtered = b2ba b
		|> filter (fun b -> Pervasives.compare b '\032' < 0 || Pervasives.compare b '\128' >= 0) in
	length filtered = 0

let isPrintable (b:bytes) =
	true
(*    Regex.IsMatch(b2ascii b, "^[a-zA-Z0-9 '()+,-.?:/=]*$")*)

let isUTF8 (b:bytes) =
	true

let isUniv (b:bytes) =
	true

let isBMP (b:bytes) =
	true

let isURI (b:bytes) =
	true

let isDate (b:bytes) =
	true
(*    Regex.IsMatch(d, "^([0-9]{2})(1[0-2]|0[0-9])(3[01]|[0-2][0-9])(2[0-3]|[01][0-9])([0-5][0-9])([0-5][0-9])Z$") *)

let isGenDate (b:bytes) =
	true
(*
	let d = b2ascii b
	Regex.IsMatch(d, "^([0-9]{4})(1[0-2]|0[0-9])(3[01]|[0-2][0-9])(2[0-3]|[01][0-9])([0-5][0-9])([0-5][0-9])Z$")
*)

let isRFC822 (b:bytes) =
	true
(*
	Regex.IsMatch(b2ascii b, @"^(?("")("".+?(?<!\\)""@)|(([0-9a-z]((\.(?!\.))|[-!#\$%&'\*\+/=\?\^`\{\}\|~\w])*"^")(?<=[0-9a-z])@))""(?(\[)(\[(\d{1,3}\.){3}\d{1,3}\])|(([0-9a-z][-\w]*[0-9a-z]*\.)+[a-z0-9][\-a-z0-9]{0,22}[a-z0-9]))$")
*)

let bTrue = create "\255"
let bFalse = create "\000"
let bEmpty = create ""

