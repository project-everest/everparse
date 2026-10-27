module EverParse3d.CAbi.ErrorCodeLowstar

module E = EverParse3d.ErrorCode

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS"]
let validator_success = E.validator_success

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED"]
let validator_error_action_failed = E.validator_error_action_failed

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA"]
let validator_error_not_enough_data = E.validator_error_not_enough_data

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_IMPOSSIBLE"]
let validator_error_impossible = E.validator_error_impossible

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE"]
let validator_error_list_size_not_multiple = E.validator_error_list_size_not_multiple

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED"]
let validator_error_constraint_failed = E.validator_error_constraint_failed

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_UNEXPECTED_PADDING"]
let validator_error_unexpected_padding = E.validator_error_unexpected_padding

[@@CMacro; FStar.Attributes.rename_let "EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED"]
let validator_error_probe_failed = E.validator_error_probe_failed

[@@FStar.Attributes.rename_let "EverParsePulseInternalErrorReasonOfResult"; FStar.Attributes.CInline]
let error_reason_of_result (code: FStar.UInt8.t) : string = E.error_reason_of_result code

[@@FStar.Attributes.rename_let "EverParsePulseInternalIsRangeOkay"; FStar.Attributes.CInline]
let error_code_is_range_okay (size offset access_size: FStar.UInt32.t) : EverParse3d.CAbi.Boolean.t =
  EverParse3d.CAbi.Boolean.of_bool (E.is_range_okay size offset access_size)
