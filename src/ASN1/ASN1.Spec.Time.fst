module ASN1.Spec.Time

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module B = FStar.Bytes
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

let is_valid_time_hh
  (hh : U32.t)
= (U32.lte hh 23ul)

let is_valid_time_hhmm
  (hh : U32.t)
  (mm : U32.t)
= (U32.lte hh 23ul) && (U32.lte mm 59ul)

let is_valid_time_hhmmss
  (hh mm ss : U32.t)
= (U32.lte hh 23ul) && (U32.lte mm 59ul) && (U32.lte ss 59ul)

let is_valid_utc_positive_timezone
  (hh mm : U32.t)
= (U32.lte hh 12ul) && (U32.lte 1ul hh) && ((U32.eq mm 0ul) || (U32.eq mm 30ul && (U32.eq hh 9ul || U32.eq hh 3ul)))

let is_valid_utc_negative_timezone
  (hh mm : U32.t)
= (U32.lte hh 14ul) && (U32.lte 1ul hh) && 
  ((U32.eq mm 0ul) || 
   (U32.eq mm 30ul && ((U32.lte 3ul hh && U32.lte hh 6ul) || (U32.eq hh 9ul) || (U32.eq hh 10ul))) || 
   (U32.eq mm 45ul && ((U32.eq hh 5ul) || (U32.eq hh 8ul) || (U32.eq hh 12ul))))

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
  (b : B.bytes)
  (s : U32.t)
  (l : U32.t {U32.v s + U32.v l <= (B.length b)})
: Tot bool (decreases (U32.v l))
= if l = 0ul then
    true
  else
    let l' = U32.sub l 1ul in
    is_valid_digit (B.index b (U32.v (U32.add s l'))) &&
    is_valid_digit_range b s l'

#push-options "--fuel 8 --split_queries"

let is_valid_yymmdd
  (b : B.bytes)
  (s : U32.t {U32.v s + 6 <= B.length b})
= if (is_valid_digit_range b s 6ul) then begin
    let yy = read_2dnum (B.index b (U32.v s))     (B.index b (U32.v s + 1)) in
    let mm = read_2dnum (B.index b (U32.v s + 2)) (B.index b (U32.v s + 3)) in
    let dd = read_2dnum (B.index b (U32.v s + 4)) (B.index b (U32.v s + 5)) in
    is_valid_calendar_date2dy yy mm dd
  end
  else 
    false

let is_valid_yyyymmdd
  (b : B.bytes)
  (s : U32.t {U32.v s + 8 <= B.length b})
= if (is_valid_digit_range b s 8ul) then begin
    let yyyy = read_4dnum (B.index b (U32.v s)) (B.index b (U32.v s + 1)) (B.index b (U32.v s + 2)) (B.index b (U32.v s + 3)) in
    let mm = read_2dnum (B.index b (U32.v s + 4)) (B.index b (U32.v s + 5)) in
    let dd = read_2dnum (B.index b (U32.v s + 6)) (B.index b (U32.v s + 7)) in
    is_valid_calendar_date4dy yyyy mm dd
  end
  else 
    false

let is_valid_hh
  (b : B.bytes)
  (s : U32.t {U32.v s + 2 <= B.length b})
= if (is_valid_digit_range b s 2ul) then begin
    let hh = read_2dnum (B.index b (U32.v s))     (B.index b (U32.v s + 1)) in
    is_valid_time_hh hh
  end
  else 
    false

let is_valid_hhmm
  (b : B.bytes)
  (s : U32.t {U32.v s + 4 <= B.length b})
= if (is_valid_digit_range b s 4ul) then begin
    let hh = read_2dnum (B.index b (U32.v s))     (B.index b (U32.v s + 1)) in
    let mm = read_2dnum (B.index b (U32.v s + 2)) (B.index b (U32.v s + 3)) in
    is_valid_time_hhmm hh mm
  end
  else 
    false

let is_valid_hhmmss
  (b : B.bytes)
  (s : U32.t {U32.v s + 6 <= B.length b})
= if (is_valid_digit_range b s 6ul) then begin
    let hh = read_2dnum (B.index b (U32.v s))     (B.index b (U32.v s + 1)) in
    let mm = read_2dnum (B.index b (U32.v s + 2)) (B.index b (U32.v s + 3)) in
    let ss = read_2dnum (B.index b (U32.v s + 4)) (B.index b (U32.v s + 5)) in
    is_valid_time_hhmmss hh mm ss
  end
  else 
    false

let is_valid_utc_timezone
  (b : B.bytes)
  (s : U32.t {U32.v s + 5 <= B.length b})
= if is_valid_digit_range b (U32.add s 1ul) 4ul then
    let hh = read_2dnum (B.index b (U32.v s + 1)) (B.index b (U32.v s + 2)) in
    let mm = read_2dnum (B.index b (U32.v s + 3)) (B.index b (U32.v s + 4)) in
    let sign = B.index b (U32.v s) in
    if (sign = 43uy) then // +
      is_valid_utc_positive_timezone hh mm
    else if (sign = 45uy) then // -
      is_valid_utc_negative_timezone hh mm
    else
      false
  else
    false

let is_valid_ASN1UTCTIME
  (b : B.bytes)
= let len = B.length b in
  if len = 11 then
    is_valid_yymmdd b 0ul && is_valid_hhmm b 6ul && B.index b 10 = 90uy
  else if len = 15 then
    is_valid_yymmdd b 0ul && is_valid_hhmm b 6ul && is_valid_utc_timezone b 10ul
  else if len = 13 then
    is_valid_yymmdd b 0ul && is_valid_hhmmss b 6ul && B.index b 12 = 90uy
  else if len = 17 then
    is_valid_yymmdd b 0ul && is_valid_hhmmss b 6ul && is_valid_utc_timezone b 12ul
  else
    false

let is_valid_localtime
  (b : B.bytes)
  (len : nat {len <= B.length b})
= if len = 10 then
    is_valid_yyyymmdd b 0ul && is_valid_hh b 8ul
  else if len = 12 then
    is_valid_yyyymmdd b 0ul && is_valid_hhmm b 8ul
  else if len = 14 then
    is_valid_yyyymmdd b 0ul && is_valid_hhmmss b 8ul
  else if 15 < len && len <= 18 then
    is_valid_yyyymmdd b 0ul && is_valid_hhmmss b 8ul && (B.index b 14 = 46uy) && (B.index b (len - 1) <> 48uy)
  else
    false

let is_valid_ASN1GENERALIZEDTIME
  (b : B.bytes)
= let len = B.length b in
  if len < 10 || len > 23 then
    false
  else
    if (B.index b (len - 1) = 90uy) then
      is_valid_localtime b (len - 1)
    else if (is_valid_digit (B.index b (len - 5))) then
        is_valid_localtime b (len - 5) && is_valid_utc_timezone b (UInt32.uint_to_t (len - 5))
      else
        is_valid_localtime b len

#pop-options

