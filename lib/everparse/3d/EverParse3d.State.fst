module EverParse3d.State
open Pulse.Lib.Pervasives
open Pulse.Lib.ForEvery

inline_for_extraction noextract
noeq type state_dict = {
  state_p: string -> prop;
  state_values: (x: string { state_p x }) -> Type0;
  state: (x: string { state_p x }) -> state_values x -> slprop;
}

let forevery_values
      (p1: string -> prop)
      (values1: (x: string { p1 x }) -> Type0)
: Tot Type0
= (x: string { p1 x }) -> values1 x

let forevery_state
      (d: state_dict)
      (v: forevery_values d.state_p d.state_values)
: Tot slprop
= forall+ (x: string { d.state_p x }) . d.state x (v x)

let state_dict_empty
: state_dict = {
  state_p = (fun _ -> False);
  state_values = (fun _ -> unit);
  state = (fun _ _ -> emp);
}

let state_dict_weaken_prop
  (d1 d2: state_dict)
: Tot prop
= (forall (x: string) . d1.state_p x ==> d2.state_p x) /\
  (forall (x: string { d1.state_p x }) . d1.state_values x == d2.state_values x) /\
  (forall (x: string { d1.state_p x }) . d1.state x == d2.state x)

let forevery_singleton_prop
  (name: string)
  (x: string)
: Tot prop
= x == name

let forevery_singleton_values
  (name: string)
  (t: Type0)
  (x: string { forevery_singleton_prop name x })
: Tot Type0
= t

let forevery_singleton_state
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
  (x: string { forevery_singleton_prop name x })
  (v: forevery_singleton_values name t x)
: Tot slprop
= state v

let state_dict_singleton
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
: state_dict = {
  state_p = forevery_singleton_prop name;
  state_values = forevery_singleton_values name t;
  state = forevery_singleton_state name state;
}
