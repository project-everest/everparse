module LowParse.SLow.BitVector
include LowParse.Spec.BitVector

(* TODO: this module is NOT intended to be extracted to C
   yet. However, OCaml extraction should work. *)

open LowParse.SLow.Combinators
open LowParse.SLow.Int
open LowParse.SLow.BoundedInt

let parse32_bv8 : parser32 parse_bv8 =
  parse32_synth'
    _
    synth_bv8
    parse32_u8
    ()

let serialize32_bv8 : serializer32 serialize_bv8 =
  serialize32_synth
    _
    synth_bv8
    _
    serialize32_u8
    synth_bv8_recip
    (fun x -> synth_bv8_recip x)
    ()

let size32_bv8 : size32 serialize_bv8 =
  size32_constant serialize_bv8 1ul ()

let rec parse32_byte_bv (n: nat) : Tot (parser32 (parse_byte_bv n)) =
  parse_byte_bv_kind_eq n;
  if n = 0
  then parse32_ret Seq.empty
  else
    parse32_synth'
      _
      (synth_byte_bv (n - 1))
      (parse32_bv8 `parse32_nondep_then` parse32_byte_bv (n - 1))
      ()

module BV = FStar.BitVector

let rec serialize32_byte_bv (n: nat { n < 4294967296 }) : Tot (serializer32 (serialize_byte_bv n)) =
  parse_byte_bv_kind_eq n;
  if n = 0
  then
    serialize32_ret Seq.empty (fun (x: BV.bv_t 0) -> assert (x `Seq.equal` Seq.empty))
  else
    serialize32_synth
      _
      (synth_byte_bv (n - 1))
      _
      (serialize32_bv8 `serialize32_nondep_then` serialize32_byte_bv (n - 1))
      (synth_byte_bv_recip (n - 1))
      (fun x -> synth_byte_bv_recip (n - 1) x)
      ()

module U32 = FStar.UInt32

let size32_byte_bv (n: nat { n < 4294967296 }) : Tot (size32 (serialize_byte_bv n)) = size32_constant _ (U32.uint_to_t n) ()

let parse32_extra_bv8 (n: nat) : Tot (parser32 (parse_extra_bv8 n)) =
  parse32_synth'
    _
    (synth_extra_bv8 n)
    (parse32_filter parse32_u8 (extra_bytes_prop n) (fun x -> extra_bytes_prop n x))
    ()

let serialize32_extra_bv8
  (n: nat)
: Tot (serializer32 (serialize_extra_bv8 n))
= serialize32_synth
    _
    (synth_extra_bv8 n)
    _
    (serialize32_filter serialize32_u8 (extra_bytes_prop n))
    (synth_extra_bv8_recip n)
    (fun x -> synth_extra_bv8_recip n x)
    ()

let size32_extra_bv8 (n: nat) : Tot (size32 (serialize_extra_bv8 n)) =
  size32_constant _ 1ul ()

let parse32_bv (n: nat) : Tot (parser32 (parse_bv n)) =
  if n % 8 = 0
  then parse32_byte_bv (n / 8)
  else parse32_synth'
    _
    (synth_bv n)
    (parse32_extra_bv8 n `parse32_nondep_then` parse32_byte_bv (n / 8))
    ()

let serialize32_bv (n: nat { n / 8 < 4294967295 }) : Tot (serializer32 (serialize_bv n)) =
  if n % 8 = 0
  then
    serialize32_byte_bv (n / 8)
  else
    serialize32_synth
      _
      (synth_bv n)
      _
      (serialize32_extra_bv8 n `serialize32_nondep_then` serialize32_byte_bv (n / 8))
      (synth_bv_recip n)
      (fun x -> synth_bv_recip n x)
      ()

let size32_bv (n: nat { n / 8 < 4294967295 }) : Tot (size32 (serialize_bv n)) =
  size32_constant _ (if n % 8 = 0 then U32.uint_to_t (n / 8) else U32.uint_to_t (1 + n / 8)) ()

let parse32_bounded_bv
  (min: nat)
  (max: nat { min <= max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 min max))
  (hp32: parser32 hp)
: Tot (parser32 (parse_bounded_bv min max hp))
= parse32_dtuple2
    hp32
    (fun (x: bounded_int32 min max) -> parse32_weaken (parse_bounded_bv_payload_kind min max) (parse32_bv (U32.v x)))

#push-options "--z3rlimit 16"

let serialize32_bounded_bv
  (min: nat)
  (max: nat { min <= max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 min max))
  (#hs: serializer hp)
  (hs32: serializer32 hs { hk.parser_kind_subkind == Some ParserStrong /\ serialize32_kind_precond hk (parse_bounded_bv_payload_kind min max) })
: Tot (serializer32 (serialize_bounded_bv min max hs))
= serialize32_dtuple2
    hs32
    (fun (x: bounded_int32 min max) -> serialize32_weaken (parse_bounded_bv_payload_kind min max) (serialize32_bv (U32.v x)))

let size32_bounded_bv
  (min: nat)
  (max: nat { min <= max })
  (#hk: parser_kind)
  (#hp: parser hk (bounded_int32 min max))
  (#hs: serializer hp)
  (hs32: size32 hs { hk.parser_kind_subkind == Some ParserStrong /\ serialize32_kind_precond hk (parse_bounded_bv_payload_kind min max) })
: Tot (size32 (serialize_bounded_bv min max hs))
= size32_dtuple2
    hs32
    (fun (x: bounded_int32 min max) -> size32_weaken (parse_bounded_bv_payload_kind min max) (size32_bv (U32.v x)))

#pop-options
