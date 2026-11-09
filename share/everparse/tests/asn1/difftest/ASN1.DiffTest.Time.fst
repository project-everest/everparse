module ASN1.DiffTest.Time

(* Differential testing (difftest/): time types.
   Must agree with difftest/schemas/{DiffTime,DiffTime2}.asn *)

open ASN1.Base
open ASN1.Syntax

let utc = asn1_utctime
let gen = asn1_generalizedtime
let date = asn1_date
let tod = asn1_time_of_day
let dateTime = asn1_date_time
