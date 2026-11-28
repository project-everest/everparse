module EverParse3d.Boolean.Actions
#lang-pulse

open Pulse.Lib.Pervasives
open EverParse3d.State
module A = EverParse3d.Actions.Base
module P = EverParse3d.ProbeActions

inline_for_extraction noextract
fn map_external_spec
  (#a #b: Type0)
  (#vt: Type0)
  (#name: string)
  (#state: vt -> slprop)
  (#spec: vt -> Tot (a & vt))
  (decode: a -> Tot b)
  (action: A.external_action_spec name state a spec)
: A.external_action_spec name state b (EverParse3d.Actions.Spec.map_extern_spec decode spec)
= (_: unit) (#w: _)
{
  let value = action () #w;
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
