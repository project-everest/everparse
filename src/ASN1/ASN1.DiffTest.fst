module ASN1.DiffTest

(* Name-based dispatch for differential testing (difftest/).
   [parse name b] is [None] if [name] is not a known "Module.Type",
   otherwise [Some r] where [r] is the number of bytes consumed by
   the parser, or [None] if it rejects. *)

open ASN1.Base
open ASN1.Spec.Interpreter
module LP = LowParse.Spec.Base

let consumed (#s: _) (k: asn1_k s) (b: bytes)
  : option nat
= match asn1_as_parser k b with
  | Some (_, n) -> Some n
  | None -> None

let parse (name: string) (b: bytes) : option (option nat)
= match name with
  | "DiffSmoke.Smoke" -> Some (consumed ASN1.DiffTest.Smoke.smoke b)
  | "DiffPrim.Bool" -> Some (consumed ASN1.DiffTest.Prim.bool_ b)
  | "DiffPrim.Int" -> Some (consumed ASN1.DiffTest.Prim.int_ b)
  | "DiffPrim.Enum" -> Some (consumed ASN1.DiffTest.Prim.enum_ b)
  | "DiffPrim.Bits" -> Some (consumed ASN1.DiffTest.Prim.bits b)
  | "DiffPrim.Octets" -> Some (consumed ASN1.DiffTest.Prim.octets b)
  | "DiffPrim.Null" -> Some (consumed ASN1.DiffTest.Prim.null_ b)
  | "DiffPrim.Oid" -> Some (consumed ASN1.DiffTest.Prim.oid b)
  | "DiffRelOid.RelOid" -> Some (consumed ASN1.DiffTest.Prim.relOid b)
  | "DiffDesc.Desc" -> Some (consumed ASN1.DiffTest.Prim.desc b)
  | "DiffIRI.Iri" -> Some (consumed ASN1.DiffTest.Prim.iri b)
  | "DiffIRI.RelIri" -> Some (consumed ASN1.DiffTest.Prim.relIri b)
  | "DiffStrings.Utf8" -> Some (consumed ASN1.DiffTest.Strings.utf8 b)
  | "DiffStrings.Numeric" -> Some (consumed ASN1.DiffTest.Strings.numeric b)
  | "DiffStrings.Printable" -> Some (consumed ASN1.DiffTest.Strings.printable b)
  | "DiffStrings.Ia5" -> Some (consumed ASN1.DiffTest.Strings.ia5 b)
  | "DiffStrings.Visible" -> Some (consumed ASN1.DiffTest.Strings.visible b)
  | "DiffStrings.Bmp" -> Some (consumed ASN1.DiffTest.Strings.bmp b)
  | "DiffStrings.Universal" -> Some (consumed ASN1.DiffTest.Strings.universal b)
  | "DiffStrings.Teletex" -> Some (consumed ASN1.DiffTest.Strings.teletex b)
  | "DiffVideotex.Videotex" -> Some (consumed ASN1.DiffTest.Strings.videotex b)
  | "DiffStrings2.Graphic" -> Some (consumed ASN1.DiffTest.Strings.graphic b)
  | "DiffStrings2.General" -> Some (consumed ASN1.DiffTest.Strings.general b)
  | "DiffTime.Utc" -> Some (consumed ASN1.DiffTest.Time.utc b)
  | "DiffTime.Gen" -> Some (consumed ASN1.DiffTest.Time.gen b)
  | "DiffTime2.Date" -> Some (consumed ASN1.DiffTest.Time.date b)
  | "DiffTime2.Tod" -> Some (consumed ASN1.DiffTest.Time.tod b)
  | "DiffTime2.DateTime" -> Some (consumed ASN1.DiffTest.Time.dateTime b)
  | "DiffConstructed.Seq" -> Some (consumed ASN1.DiffTest.Constructed.seq b)
  | "DiffConstructed.IntSeq" -> Some (consumed ASN1.DiffTest.Constructed.intSeq b)
  | "DiffConstructed.OctetsSet" -> Some (consumed ASN1.DiffTest.Constructed.octetsSet b)
  | "DiffConstructed.Choice" -> Some (consumed ASN1.DiffTest.Constructed.choice b)
  | "DiffConstructed.App" -> Some (consumed ASN1.DiffTest.Constructed.app b)
  | "DiffConstructed.PrivExp" -> Some (consumed ASN1.DiffTest.Constructed.privExp b)
  | "DiffConstructed.HighCtx" -> Some (consumed ASN1.DiffTest.Constructed.highCtx b)
  | "DiffConstructed.HighApp" -> Some (consumed ASN1.DiffTest.Constructed.highApp b)
  | "DiffConstructed.Nested" -> Some (consumed ASN1.DiffTest.Constructed.nested b)
  | "DiffSet.Set" -> Some (consumed ASN1.DiffTest.Set.set_ b)
  | "DiffAny.AnyT" -> Some (consumed ASN1.DiffTest.Any.anyT b)
  | "DiffAny.AlgId" -> Some (consumed ASN1.DiffTest.Any.algId b)
  | "DiffExternal.Ext" -> Some (consumed ASN1.DiffTest.Presentation.ext b)
  | "DiffPdv.Pdv" -> Some (consumed ASN1.DiffTest.Presentation.pdv b)
  | "DiffCharStr.CharStr" -> Some (consumed ASN1.DiffTest.Presentation.charStr b)
  | "DiffConstraints.Sized" -> Some (consumed ASN1.DiffTest.Constraints.sized b)
  | "DiffConstraints.Byte" -> Some (consumed ASN1.DiffTest.Constraints.byte b)
  | "DiffConstraints.NonEmptySeqOf" -> Some (consumed ASN1.DiffTest.Constraints.nonEmptySeqOf b)
  | "DiffConstraints.NonEmptySetOf" -> Some (consumed ASN1.DiffTest.Constraints.nonEmptySetOf b)
  | _ -> None
