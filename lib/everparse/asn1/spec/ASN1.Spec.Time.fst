module ASN1.Spec.Time

open ASN1.Bytes

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Cast = FStar.Int.Cast

let days_of_month
  (is_leap : bool)
  (mm : U32.t {U32.lte 1ul mm /\ U32.lte mm 12ul})
= if U32.lte mm 6ul then
    if U32.lte mm 3ul then
      if U32.eq mm 1ul then
        31ul
      else if U32.eq mm 2ul then
        if is_leap then
          29ul
        else
          28ul
      else
        31ul
    else 
      if U32.eq mm 4ul then
        30ul
      else if U32.eq mm 5ul then
        31ul
      else 
        30ul
  else
    if U32.lte mm 9ul then
      if U32.eq mm 7ul then
        31ul
      else if U32.eq mm 8ul then
        31ul
      else
        30ul
    else
      if U32.eq mm 10ul then
        31ul
      else if U32.eq mm 11ul then
        30ul
      else
        31ul

let is_valid_calendar_date2dy
  (yy : U32.t)
  (mm : U32.t)
  (dd : U32.t)
= if U32.lte 100ul yy then
    false
  else 
    if U32.lt mm 1ul || U32.lt 12ul mm then
      false
    else begin
      let is_leap = (U32.eq (U32.rem yy 4ul) 0ul) in
      if (U32.lte 1ul dd) && (U32.lte dd (days_of_month is_leap mm)) then
        true
      else
        false
    end

let is_valid_calendar_date4dy
  (yyyy : U32.t)
  (mm : U32.t)
  (dd : U32.t)
= if U32.lte 10000ul yyyy then
    false
  else 
    if U32.lt mm 1ul || U32.lt 12ul mm then
      false
    else begin
      let is_leap = (U32.eq (U32.rem yyyy 4ul) 0ul) && ((U32.eq (U32.rem yyyy 100ul) 0ul) = false || (U32.eq (U32.rem yyyy 400ul) 0ul)) in
      if (U32.lte 1ul dd) && (U32.lte dd (days_of_month is_leap mm)) then
        true
      else
        false
    end

(* Leap seconds: UTCTime and GeneralizedTime are in UTC in DER (X.690 11.7,
   11.8), where a leap second can only be 23:59:60. TIME-OF-DAY and DATE-TIME
   are local times, where a leap second can occur at the end of any minute. *)
let is_valid_time_hhmmss
  (utc : bool)
  (hh mm ss : U32.t)
= (U32.lte hh 23ul) && (U32.lte mm 59ul) &&
  (U32.lte ss 59ul ||
   (ss = 60ul && (not utc || (hh = 23ul && mm = 59ul))))

let is_valid_digit
  (ch : U8.t)
= U8.lte 48uy ch && U8.lte ch 57uy 

let read_digit
  (ch : U8.t)
: Pure U32.t
  (requires is_valid_digit ch)
  (ensures fun d -> U32.lte 0ul d /\ U32.lte d 9ul) 
= let d = U8.sub ch 48uy in
  Cast.uint8_to_uint32 d

let read_2dnum
  (ch1 : U8.t {is_valid_digit ch1})
  (ch2 : U8.t {is_valid_digit ch2})
= (U32.add (U32.mul (read_digit ch1) 10ul) (read_digit ch2))

let read_4dnum
  (ch1 : U8.t {is_valid_digit ch1})
  (ch2 : U8.t {is_valid_digit ch2})
  (ch3 : U8.t {is_valid_digit ch3})
  (ch4 : U8.t {is_valid_digit ch4})
= (U32.add (U32.mul (U32.add (U32.mul (U32.add (U32.mul (read_digit ch1) 10ul) (read_digit ch2)) 10ul) (read_digit ch3)) 10ul) (read_digit ch4))

let rec is_valid_digit_range
  (b : asn1_bytes)
  (s : nat)
  (l : nat {s + l <= Seq.length b})
: Tot bool (decreases l)
= if l = 0 then
    true
  else
    let l' = l - 1 in
    is_valid_digit (Seq.index b (s + l')) &&
    is_valid_digit_range b s l'

#push-options "--fuel 8"

let is_valid_yymmdd
  (b : asn1_bytes)
  (s : U32.t {U32.v s + 6 <= Seq.length b})
= if (is_valid_digit_range b (U32.v s) 6) then begin
    let yy = read_2dnum (Seq.index b (U32.v s))     (Seq.index b (U32.v s + 1)) in
    let mm = read_2dnum (Seq.index b (U32.v s + 2)) (Seq.index b (U32.v s + 3)) in
    let dd = read_2dnum (Seq.index b (U32.v s + 4)) (Seq.index b (U32.v s + 5)) in
    is_valid_calendar_date2dy yy mm dd
  end
  else 
    false

let is_valid_yyyymmdd
  (b : asn1_bytes)
  (s : U32.t {U32.v s + 8 <= Seq.length b})
= if (is_valid_digit_range b (U32.v s) 8) then begin
    let yyyy = read_4dnum (Seq.index b (U32.v s)) (Seq.index b (U32.v s + 1)) (Seq.index b (U32.v s + 2)) (Seq.index b (U32.v s + 3)) in
    let mm = read_2dnum (Seq.index b (U32.v s + 4)) (Seq.index b (U32.v s + 5)) in
    let dd = read_2dnum (Seq.index b (U32.v s + 6)) (Seq.index b (U32.v s + 7)) in
    is_valid_calendar_date4dy yyyy mm dd
  end
  else 
    false

let is_valid_hhmmss
  (utc : bool)
  (b : asn1_bytes)
  (s : U32.t {U32.v s + 6 <= Seq.length b})
= if (is_valid_digit_range b (U32.v s) 6) then begin
    let hh = read_2dnum (Seq.index b (U32.v s))     (Seq.index b (U32.v s + 1)) in
    let mm = read_2dnum (Seq.index b (U32.v s + 2)) (Seq.index b (U32.v s + 3)) in
    let ss = read_2dnum (Seq.index b (U32.v s + 4)) (Seq.index b (U32.v s + 5)) in
    is_valid_time_hhmmss utc hh mm ss
  end
  else 
    false

(* X.690 11.8: a DER UTCTime is exactly YYMMDDhhmmssZ. *)
let is_valid_ASN1UTCTIME
  (b : asn1_bytes)
= Seq.length b = 13 &&
  is_valid_yymmdd b 0ul && is_valid_hhmmss true b 6ul && Seq.index b 12 = 90uy // Z

(* X.690 11.7: a DER GeneralizedTime is YYYYMMDDhhmmss[.f+]Z, where the
   fractional part, if present, is non-empty and has no trailing zero. *)
let is_valid_ASN1GENERALIZEDTIME
  (b : asn1_bytes)
= let len = Seq.length b in
  if len = 15 then
    is_valid_yyyymmdd b 0ul && is_valid_hhmmss true b 8ul && Seq.index b 14 = 90uy // Z
  else if len >= 17 then
    is_valid_yyyymmdd b 0ul && is_valid_hhmmss true b 8ul &&
    Seq.index b 14 = 46uy && // .
    is_valid_digit_range b 15 (len - 16) &&
    Seq.index b (len - 2) <> 48uy && // no trailing 0
    Seq.index b (len - 1) = 90uy // Z
  else
    false

(* X.680 38.4: DATE, TIME-OF-DAY and DATE-TIME are TIME subtypes with
   "Year=Basic" (years 1582 to 9999) and "Time=HMS" settings, encoded as
   YYYYMMDD, hhmmss and YYYYMMDDhhmmss respectively (X.690 8.26). *)
let is_valid_basic_year
  (b : asn1_bytes)
  (s : U32.t {U32.v s + 4 <= Seq.length b})
= is_valid_digit_range b (U32.v s) 4 &&
  U32.lte 1582ul (read_4dnum (Seq.index b (U32.v s)) (Seq.index b (U32.v s + 1)) (Seq.index b (U32.v s + 2)) (Seq.index b (U32.v s + 3)))

let is_valid_ASN1DATE
  (b : asn1_bytes)
= Seq.length b = 8 &&
  is_valid_yyyymmdd b 0ul && is_valid_basic_year b 0ul

let is_valid_ASN1TIMEOFDAY
  (b : asn1_bytes)
= Seq.length b = 6 &&
  is_valid_hhmmss false b 0ul

let is_valid_ASN1DATETIME
  (b : asn1_bytes)
= Seq.length b = 14 &&
  is_valid_yyyymmdd b 0ul && is_valid_basic_year b 0ul && is_valid_hhmmss false b 8ul

#pop-options

