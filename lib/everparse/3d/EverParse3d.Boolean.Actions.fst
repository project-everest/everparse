module EverParse3d.Boolean.Actions
#lang-pulse

open Pulse.Lib.Pervasives
open EverParse3d.State
module A = EverParse3d.Actions.Base
module P = EverParse3d.ProbeActions

inline_for_extraction noextract
fn map_external
  (#a #b: Type0)
  (#d: state_dict)
  (decode: a -> Tot b)
  (action: A.external_action d a)
: A.external_action d b
= (_: unit)
{
  let value = action ();
  decode value
}

inline_for_extraction noextract
fn map_pure
  (#a #b: Type0)
  (decode: a -> Tot b)
  (action: P.pure_external_action a)
: P.pure_external_action b
= (_: unit)
{
  let value = action ();
  decode value
}
