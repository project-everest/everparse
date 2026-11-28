module ASN1.Pulse.Checkers
#lang-pulse
(* Executable checkers for the byte-level validity predicates of the ASN.1
   terminal types whose content is the whole input, filtered by a predicate
   (UTF8String, BMPString, UniversalString, OID-IRI, RELATIVE-OID-IRI and the
   time types). Each checker is a separate C function. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Spec.Base
open ASN1.Base
open ASN1.Spec.Time
open ASN1.Spec.IRI

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference

let slice_checker (f: bytes -> GTot bool) =
  (s: S.slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt bool (pts_to s #pm v) (fun r -> pts_to s #pm v ** pure (r == f v))

(* BIT STRING: initial octet (unused bits, X.690 8.6.2.2) followed by the
   payload, whose unused bits must be zero in DER (X.690 11.2.1) *)

let bitstring_ok (b: bytes) : GTot bool =
  Seq.length b > 0 &&
  ASN1.Spec.Content.BITSTRING.filter_asn1_bitstring_unused (Seq.index b 0) &&
  ASN1.Spec.Content.BITSTRING.filter_asn1_bitstring_payload (Seq.index b 0) (Seq.slice b 1 (Seq.length b))

let bitstring_mask_lemma (u: U8.t { U8.v u <= 7 }) (last: U8.t)
: Lemma (
    let m = U8.shift_left 1uy (FStar.Int.Cast.uint8_to_uint32 u) in
    U8.v m > 0 /\
    U8.v (U8.rem last m) == FStar.UInt.mod (U8.v last) (pow2 (U8.v u)))
= FStar.Math.Lemmas.pow2_le_compat 7 (U8.v u);
  FStar.Math.Lemmas.small_mod (pow2 (U8.v u)) (pow2 8)

fn check_bitstring
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == bitstring_ok v)
{
  S.pts_to_len s;
  let len = S.len s;
  if (len = 0sz) {
    false
  } else {
    let u = s.(0sz);
    if (U8.lte u 7uy) {
      if (u = 0uy) {
        true
      } else if (len = 1sz) {
        false
      } else {
        let last = s.(SZ.sub len 1sz);
        bitstring_mask_lemma u last;
        (U8.rem last (U8.shift_left 1uy (FStar.Int.Cast.uint8_to_uint32 u)) = 0uy)
      }
    } else {
      false
    }
  }
}

(* UTF8String *)

fn check_utf8
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == LowParse.Spec.UTF8.correct v)
{
  LowParse.Pulse.UTF8.impl_utf8_correct s
}

(* BMPString *)

fn check_bmp
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_bmp v)
{
  S.pts_to_len s;
  let len = S.len s;
  let mut pres = true;
  let mut pi = 0sz;
  while (
    let res = !pres;
    let i = !pi;
    (res && SZ.lt i len)
  ) invariant exists* res i .
    pts_to s #pm v **
    pts_to pres res **
    pts_to pi i **
    pure (
      SZ.v i <= Seq.length v /\
      is_valid_bmp v == (res && is_valid_bmp_from v (SZ.v i))
    )
    decreases %[(if !pres then 1 else 0); (SZ.v len - SZ.v (!pi))]
  {
    let i = !pi;
    if (SZ.lt (SZ.sub len i) 2sz) {
      pres := false
    } else {
      let hi = s.(i);
      if (U8.lte 0xD8uy hi && U8.lte hi 0xDFuy) {
        pres := false
      } else {
        pi := SZ.add i 2sz
      }
    }
  };
  !pres
}

(* UniversalString *)

fn check_universal
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_universal v)
{
  S.pts_to_len s;
  let len = S.len s;
  let mut pres = true;
  let mut pi = 0sz;
  while (
    let res = !pres;
    let i = !pi;
    (res && SZ.lt i len)
  ) invariant exists* res i .
    pts_to s #pm v **
    pts_to pres res **
    pts_to pi i **
    pure (
      SZ.v i <= Seq.length v /\
      is_valid_universal v == (res && is_valid_universal_from v (SZ.v i))
    )
    decreases %[(if !pres then 1 else 0); (SZ.v len - SZ.v (!pi))]
  {
    let i = !pi;
    if (SZ.lt (SZ.sub len i) 4sz) {
      pres := false
    } else {
      let b0 = s.(i);
      let b1 = s.(SZ.add i 1sz);
      let b2 = s.(SZ.add i 2sz);
      if (b0 = 0uy && U8.lte b1 0x10uy && not (b1 = 0uy && U8.lte 0xD8uy b2 && U8.lte b2 0xDFuy)) {
        pi := SZ.add i 4sz
      } else {
        pres := false
      }
    }
  };
  !pres
}

(* Character counts, for SizeConstraint on character strings *)

let slice_counter (f: bytes -> GTot nat) =
  (s: S.slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t (pts_to s #pm v) (fun r -> pts_to s #pm v ** pure (SZ.v r == f v))

fn count_utf8
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: SZ.t
ensures pts_to s #pm v ** pure (SZ.v r == utf8_count v)
{
  S.pts_to_len s;
  let len = S.len s;
  let mut pn = 0sz;
  let mut pi = 0sz;
  while (
    let i = !pi;
    SZ.lt i len
  ) invariant exists* n i .
    pts_to s #pm v **
    pts_to pn n **
    pts_to pi i **
    pure (
      SZ.v i <= Seq.length v /\
      SZ.v n <= SZ.v i /\
      SZ.v n + utf8_count_from v (SZ.v i) == utf8_count v
    )
    decreases (SZ.v len - SZ.v (!pi))
  {
    let i = !pi;
    let c = s.(i);
    let n = !pn;
    if (U8.lt c 128uy || U8.gte c 192uy) {
      pn := SZ.add n 1sz
    };
    pi := SZ.add i 1sz
  };
  !pn
}

(* OID-IRI and RELATIVE-OID-IRI *)

#push-options "--z3rlimit 32"

inline_for_extraction
let is_iri_digit_impl (c: U8.t) : Tot (b: bool { b == is_iri_digit c }) =
  U8.lte 48uy c && U8.lte c 57uy

inline_for_extraction
let is_iri_label_char_impl (c: U8.t) : Tot (b: bool { b == is_iri_label_char c }) =
  U8.gte c 128uy ||
  (U8.lte 65uy c && U8.lte c 90uy) ||
  (U8.lte 97uy c && U8.lte c 122uy) ||
  is_iri_digit_impl c ||
  c = 45uy || c = 46uy || c = 95uy || c = 126uy

fn check_iri_labels
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (start0: SZ.t)
requires pts_to s #pm v ** pure (SZ.v start0 <= Seq.length v)
returns r: bool
ensures pts_to s #pm v ** pure (SZ.v start0 <= Seq.length v /\ r == iri_labels_ok v (SZ.v start0) (SZ.v start0) true)
{
  S.pts_to_len s;
  let len = S.len s;
  let mut pcont = true;
  let mut pres = true;
  let mut pstart = start0;
  let mut pi = start0;
  let mut pdigits = true;
  while (
    !pcont
  ) invariant exists* cont res start i digits .
    pts_to s #pm v **
    pts_to pcont cont **
    pts_to pres res **
    pts_to pstart start **
    pts_to pi i **
    pts_to pdigits digits **
    pure (
      SZ.v start <= SZ.v i /\ SZ.v i <= Seq.length v /\
      iri_labels_ok v (SZ.v start0) (SZ.v start0) true ==
        (if cont then iri_labels_ok v (SZ.v start) (SZ.v i) digits else res)
    )
    decreases %[(if !pcont then 1 else 0); (SZ.v len - SZ.v (!pi))]
  {
    let i = !pi;
    let start = !pstart;
    let digits = !pdigits;
    let at_end = (i = len);
    let at_slash = (if at_end then true else (s.(i) = iri_slash));
    if (at_slash) {
      let nonempty = SZ.gt i start;
      let no_leading_zero = (if (not digits || not nonempty) then true else (if (SZ.sub i start = 1sz) then true else (s.(start) <> 48uy)));
      if (nonempty && no_leading_zero) {
        if (at_end) {
          pcont := false;
          pres := true
        } else {
          pstart := SZ.add i 1sz;
          pi := SZ.add i 1sz;
          pdigits := true
        }
      } else {
        pcont := false;
        pres := false
      }
    } else {
      let c = s.(i);
      if (is_iri_label_char_impl c) {
        pi := SZ.add i 1sz;
        pdigits := (digits && is_iri_digit_impl c)
      } else {
        pcont := false;
        pres := false
      }
    }
  };
  !pres
}

#pop-options

fn check_relative_oid_iri
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_relative_oid_iri v)
{
  let ok = check_utf8 s;
  if (ok) {
    check_iri_labels s 0sz
  } else {
    false
  }
}

fn check_oid_iri
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_oid_iri v)
{
  S.pts_to_len s;
  let ok = check_utf8 s;
  if (ok && SZ.gt (S.len s) 0sz) {
    let c0 = s.(0sz);
    if (c0 = iri_slash) {
      check_iri_labels s 1sz
    } else {
      false
    }
  } else {
    false
  }
}

(* Time types *)

fn check_digit_range
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (st: SZ.t)
  (l0: SZ.t)
requires pts_to s #pm v ** pure (SZ.v st + SZ.v l0 <= Seq.length v)
returns r: bool
ensures pts_to s #pm v ** pure (SZ.v st + SZ.v l0 <= Seq.length v /\ r == is_valid_digit_range v (SZ.v st) (SZ.v l0))
{
  S.pts_to_len s;
  let mut pres = true;
  let mut pl = l0;
  while (
    let res = !pres;
    let l = !pl;
    (res && SZ.gt l 0sz)
  ) invariant exists* res l .
    pts_to s #pm v **
    pts_to pres res **
    pts_to pl l **
    pure (
      SZ.v l <= SZ.v l0 /\
      is_valid_digit_range v (SZ.v st) (SZ.v l0) == (res && is_valid_digit_range v (SZ.v st) (SZ.v l))
    )
    decreases %[(if !pres then 1 else 0); SZ.v (!pl)]
  {
    let l = !pl;
    let l' = SZ.sub l 1sz;
    let c = s.(SZ.add st l');
    if (is_valid_digit c) {
      pl := l'
    } else {
      pres := false
    }
  };
  !pres
}

#push-options "--fuel 8 --z3rlimit 64"

fn check_yymmdd
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (st: U32.t)
requires pts_to s #pm v ** pure (U32.v st + 6 <= Seq.length v)
returns r: bool
ensures pts_to s #pm v ** pure (U32.v st + 6 <= Seq.length v /\ r == is_valid_yymmdd v st)
{
  S.pts_to_len s;
  SZ.fits_lte (U32.v st) (SZ.v (S.len s));
  let i = SZ.uint32_to_sizet st;
  let ok = check_digit_range s i 6sz;
  if (ok) {
    let c0 = s.(i);
    let c1 = s.(SZ.add i 1sz);
    let c2 = s.(SZ.add i 2sz);
    let c3 = s.(SZ.add i 3sz);
    let c4 = s.(SZ.add i 4sz);
    let c5 = s.(SZ.add i 5sz);
    is_valid_calendar_date2dy (read_2dnum c0 c1) (read_2dnum c2 c3) (read_2dnum c4 c5)
  } else {
    false
  }
}

fn check_yyyymmdd
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (st: U32.t)
requires pts_to s #pm v ** pure (U32.v st + 8 <= Seq.length v)
returns r: bool
ensures pts_to s #pm v ** pure (U32.v st + 8 <= Seq.length v /\ r == is_valid_yyyymmdd v st)
{
  S.pts_to_len s;
  SZ.fits_lte (U32.v st) (SZ.v (S.len s));
  let i = SZ.uint32_to_sizet st;
  let ok = check_digit_range s i 8sz;
  if (ok) {
    let c0 = s.(i);
    let c1 = s.(SZ.add i 1sz);
    let c2 = s.(SZ.add i 2sz);
    let c3 = s.(SZ.add i 3sz);
    let c4 = s.(SZ.add i 4sz);
    let c5 = s.(SZ.add i 5sz);
    let c6 = s.(SZ.add i 6sz);
    let c7 = s.(SZ.add i 7sz);
    is_valid_calendar_date4dy (read_4dnum c0 c1 c2 c3) (read_2dnum c4 c5) (read_2dnum c6 c7)
  } else {
    false
  }
}

fn check_hhmmss
  (utc: bool)
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (st: U32.t)
requires pts_to s #pm v ** pure (U32.v st + 6 <= Seq.length v)
returns r: bool
ensures pts_to s #pm v ** pure (U32.v st + 6 <= Seq.length v /\ r == is_valid_hhmmss utc v st)
{
  S.pts_to_len s;
  SZ.fits_lte (U32.v st) (SZ.v (S.len s));
  let i = SZ.uint32_to_sizet st;
  let ok = check_digit_range s i 6sz;
  if (ok) {
    let c0 = s.(i);
    let c1 = s.(SZ.add i 1sz);
    let c2 = s.(SZ.add i 2sz);
    let c3 = s.(SZ.add i 3sz);
    let c4 = s.(SZ.add i 4sz);
    let c5 = s.(SZ.add i 5sz);
    is_valid_time_hhmmss utc (read_2dnum c0 c1) (read_2dnum c2 c3) (read_2dnum c4 c5)
  } else {
    false
  }
}

fn check_basic_year
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (st: U32.t)
requires pts_to s #pm v ** pure (U32.v st + 4 <= Seq.length v)
returns r: bool
ensures pts_to s #pm v ** pure (U32.v st + 4 <= Seq.length v /\ r == is_valid_basic_year v st)
{
  S.pts_to_len s;
  SZ.fits_lte (U32.v st) (SZ.v (S.len s));
  let i = SZ.uint32_to_sizet st;
  let ok = check_digit_range s i 4sz;
  if (ok) {
    let c0 = s.(i);
    let c1 = s.(SZ.add i 1sz);
    let c2 = s.(SZ.add i 2sz);
    let c3 = s.(SZ.add i 3sz);
    U32.lte 1582ul (read_4dnum c0 c1 c2 c3)
  } else {
    false
  }
}

#pop-options

let utctime_last (v: bytes)
: Lemma (requires Seq.length v == 13 /\ is_valid_yymmdd v 0ul /\ is_valid_hhmmss true v 6ul)
  (ensures is_valid_ASN1UTCTIME v == (Seq.index v 12 = 90uy))
= ()

fn check_utctime
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_ASN1UTCTIME v)
{
  S.pts_to_len s;
  if (S.len s = 13sz) {
    let a = check_yymmdd s 0ul;
    if (a) {
      let b = check_hhmmss true s 6ul;
      if (b) {
        let z = s.(12sz);
        utctime_last v;
        (z = 90uy)
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}

#push-options "--z3rlimit 32"

fn check_generalizedtime
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_ASN1GENERALIZEDTIME v)
{
  S.pts_to_len s;
  let len = S.len s;
  if (len = 15sz || SZ.gte len 17sz) {
    let a = check_yyyymmdd s 0ul;
    if (a) {
      let b = check_hhmmss true s 8ul;
      if (b) {
        if (len = 15sz) {
          let z = s.(14sz);
          (z = 90uy)
        } else {
          let dot = s.(14sz);
          if (dot = 46uy) {
            let d = check_digit_range s 15sz (SZ.sub len 16sz);
            if (d) {
              let last0 = s.(SZ.sub len 2sz);
              let z = s.(SZ.sub len 1sz);
              (last0 <> 48uy && z = 90uy)
            } else {
              false
            }
          } else {
            false
          }
        }
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}

#pop-options

fn check_date
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_ASN1DATE v)
{
  S.pts_to_len s;
  if (S.len s = 8sz) {
    let a = check_yyyymmdd s 0ul;
    if (a) {
      check_basic_year s 0ul
    } else {
      false
    }
  } else {
    false
  }
}

fn check_timeofday
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_ASN1TIMEOFDAY v)
{
  S.pts_to_len s;
  if (S.len s = 6sz) {
    check_hhmmss false s 0ul
  } else {
    false
  }
}

fn check_datetime
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
requires pts_to s #pm v
returns r: bool
ensures pts_to s #pm v ** pure (r == is_valid_ASN1DATETIME v)
{
  S.pts_to_len s;
  if (S.len s = 14sz) {
    let a = check_yyyymmdd s 0ul;
    if (a) {
      let b = check_basic_year s 0ul;
      if (b) {
        check_hhmmss false s 8ul
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}
