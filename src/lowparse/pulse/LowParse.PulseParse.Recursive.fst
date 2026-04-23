module LowParse.PulseParse.Recursive
(* All combinators in LowParse.Pulse.Recursive (validate_recursive, jump_recursive,
   impl_pred_recursive, etc.) fundamentally require serialize_recursive_param,
   which bundles a serializer for the recursive data type. The validation and
   jumping logic uses serializer-based splitting (split_dtuple2, pts_to_serialized_synth_*,
   pts_to_serialized_ext_trade) throughout, making it infeasible to port to
   pts_to_parsed without a complete redesign of the recursive parsing infrastructure. *)
