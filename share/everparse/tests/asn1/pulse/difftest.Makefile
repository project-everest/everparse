# The differential test validators, included by ./Makefile and by
# EverParse's src/ASN1/pulse/Makefile (oracle tests).
#
# For each test <T>: extraction root module ASN1.Pulse.DiffTest.<T>.module,
# vectors file (in ../difftest/vectors), ASN.1 type, and entry point
# (validator name in that module)
C_TESTS := Smoke
Smoke.module := Smoke
Smoke.vectors := smoke.json
Smoke.type := DiffSmoke.Smoke
Smoke.entry := validate_smoke

# <T> <module> <vectors> <ASN.1 type> <entry>
define difftest_case
C_TESTS += $(1)
$(1).module := $(2)
$(1).vectors := $(3)
$(1).type := $(4)
$(1).entry := $(5)
endef

$(eval $(call difftest_case,Prim_Bool,Prim,prim.json,DiffPrim.Bool,validate_bool_))
$(eval $(call difftest_case,Prim_Int,Prim,prim.json,DiffPrim.Int,validate_int_))
$(eval $(call difftest_case,Prim_Bits,Prim,prim.json,DiffPrim.Bits,validate_bits))
$(eval $(call difftest_case,Prim_Octets,Prim,prim.json,DiffPrim.Octets,validate_octets))
$(eval $(call difftest_case,Prim_Null,Prim,prim.json,DiffPrim.Null,validate_null_))
$(eval $(call difftest_case,Prim_Oid,Prim,prim.json,DiffPrim.Oid,validate_oid))
$(eval $(call difftest_case,Prim_RelOid,Prim,prim.json,DiffRelOid.RelOid,validate_relOid))
$(eval $(call difftest_case,Prim_Desc,Prim,prim.json,DiffDesc.Desc,validate_desc))
$(eval $(call difftest_case,Prim_Iri,Prim,prim.json,DiffIRI.Iri,validate_iri))
$(eval $(call difftest_case,Prim_RelIri,Prim,prim.json,DiffIRI.RelIri,validate_relIri))
$(eval $(call difftest_case,Prim_Enum,Prim,prim.json,DiffPrim.Enum,validate_enum_))
$(eval $(call difftest_case,Strings_Utf8,Strings,strings.json,DiffStrings.Utf8,validate_utf8))
$(eval $(call difftest_case,Strings_Numeric,Strings,strings.json,DiffStrings.Numeric,validate_numeric))
$(eval $(call difftest_case,Strings_Printable,Strings,strings.json,DiffStrings.Printable,validate_printable))
$(eval $(call difftest_case,Strings_Ia5,Strings,strings.json,DiffStrings.Ia5,validate_ia5))
$(eval $(call difftest_case,Strings_Visible,Strings,strings.json,DiffStrings.Visible,validate_visible))
$(eval $(call difftest_case,Strings_Bmp,Strings,strings.json,DiffStrings.Bmp,validate_bmp))
$(eval $(call difftest_case,Strings_Universal,Strings,strings.json,DiffStrings.Universal,validate_universal))
$(eval $(call difftest_case,Strings_Teletex,Strings,strings.json,DiffStrings.Teletex,validate_teletex))
$(eval $(call difftest_case,Strings_Videotex,Strings,strings.json,DiffVideotex.Videotex,validate_videotex))
$(eval $(call difftest_case,Strings_Graphic,Strings,strings.json,DiffStrings2.Graphic,validate_graphic))
$(eval $(call difftest_case,Strings_General,Strings,strings.json,DiffStrings2.General,validate_general))
$(eval $(call difftest_case,Time_Utc,Time,time.json,DiffTime.Utc,validate_utc))
$(eval $(call difftest_case,Time_Gen,Time,time.json,DiffTime.Gen,validate_gen))
$(eval $(call difftest_case,Time_Date,Time,time.json,DiffTime2.Date,validate_date))
$(eval $(call difftest_case,Time_Tod,Time,time.json,DiffTime2.Tod,validate_tod))
$(eval $(call difftest_case,Time_DateTime,Time,time.json,DiffTime2.DateTime,validate_dateTime))
$(eval $(call difftest_case,Constructed_Seq,Constructed,constructed.json,DiffConstructed.Seq,validate_seq))
$(eval $(call difftest_case,Constructed_IntSeq,Constructed,constructed.json,DiffConstructed.IntSeq,validate_intSeq))
$(eval $(call difftest_case,Constructed_Choice,Constructed,constructed.json,DiffConstructed.Choice,validate_choice))
$(eval $(call difftest_case,Constructed_App,Constructed,constructed.json,DiffConstructed.App,validate_app))
$(eval $(call difftest_case,Constructed_PrivExp,Constructed,constructed.json,DiffConstructed.PrivExp,validate_privExp))
$(eval $(call difftest_case,Constructed_HighCtx,Constructed,constructed.json,DiffConstructed.HighCtx,validate_highCtx))
$(eval $(call difftest_case,Constructed_HighApp,Constructed,constructed.json,DiffConstructed.HighApp,validate_highApp))
$(eval $(call difftest_case,Constructed_Nested,Constructed,constructed.json,DiffConstructed.Nested,validate_nested))
$(eval $(call difftest_case,Constructed_OctetsSet,Constructed,constructed.json,DiffConstructed.OctetsSet,validate_octetsSet))
$(eval $(call difftest_case,Constraints_Sized,Constraints,constraints.json,DiffConstraints.Sized,validate_sized))
$(eval $(call difftest_case,Constraints_Byte,Constraints,constraints.json,DiffConstraints.Byte,validate_byte))
$(eval $(call difftest_case,Constraints_NonEmptySeqOf,Constraints,constraints.json,DiffConstraints.NonEmptySeqOf,validate_nonEmptySeqOf))
$(eval $(call difftest_case,Constraints_NonEmptySetOf,Constraints,constraints.json,DiffConstraints.NonEmptySetOf,validate_nonEmptySetOf))
$(eval $(call difftest_case,Set_Set,Set,set.json,DiffSet.Set,validate_set))
$(eval $(call difftest_case,Any_AnyT,Any,any.json,DiffAny.AnyT,validate_anyT))
$(eval $(call difftest_case,Any_AlgId,Any,any.json,DiffAny.AlgId,validate_algId))
$(eval $(call difftest_case,Presentation_Ext,Presentation,presentation.json,DiffExternal.Ext,validate_ext))
$(eval $(call difftest_case,Presentation_Pdv,Presentation,presentation.json,DiffPdv.Pdv,validate_pdv))
$(eval $(call difftest_case,Presentation_CharStr,Presentation,presentation.json,DiffCharStr.CharStr,validate_charStr))

DIFFTEST_MODULES := $(sort $(foreach t,$(C_TESTS),ASN1.Pulse.DiffTest.$($(t).module)))
