module Hashtable
open FStar.All
val t (key:eqtype) (value:Type0) : Type0
val create (#key:eqtype) (#value:Type) (n:int) : ML (t key value)
val try_find (#key:eqtype) (#value:Type) (h:t key value) (k:key) : ML (option value)
val insert (#key:eqtype) (#value:Type) (h:t key value) (k:key) (v:value) : ML unit
val remove (#key:eqtype) (#value:Type) (h:t key value) (k:key) : ML unit
val fold (#key:eqtype) (#value:Type) (f:key -> value -> 'a -> ML 'a) (h:t key value) (a:'a) : ML 'a
val iter (#key:eqtype) (#value:Type) (f:key -> value -> ML unit) (h:t key value) : ML unit
val length (#key:eqtype) (#value:Type) (h:t key value) : ML int
