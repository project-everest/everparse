module EverParse3d.CAbi.ErrorCodePulse

module E = EverParse3d.ErrorCode

[@@FStar.Attributes.rename_let "EverParseErrorReasonOfResult"; FStar.Attributes.CInline]
let error_reason_of_result (code: FStar.UInt8.t) : string = E.error_reason_of_result code

[@@FStar.Attributes.rename_let "EverParseIsRangeOkay"; FStar.Attributes.CInline]
let error_code_is_range_okay (size offset access_size: FStar.UInt32.t) : EverParse3d.CAbi.Boolean.t =
  EverParse3d.CAbi.Boolean.of_bool (E.is_range_okay size offset access_size)
