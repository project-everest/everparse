module ASN1.Debug
open LowParse.Tot.Base

val parse_debug
  (#t: Type)
  (#k: parser_kind)
  (msg: string)
  (p: parser k t)
: Pure (parser k t)
    (requires True)
    (ensures (fun f -> forall input . parse f input == parse p input))

val print_debug
  (#t: Type)
  (msg: string)
  (v: t)
: Pure t
    (requires True)
    (ensures (fun v' -> v' == v))

val parse_debugf
  (#t #t': Type)
  (#k: parser_kind)
  (msg: string)
  (fp: t' -> parser k t)
: Pure (t' -> parser k t)
    (requires True)
    (ensures (fun f -> forall x input . parse (f x) input == parse (fp x) input))
