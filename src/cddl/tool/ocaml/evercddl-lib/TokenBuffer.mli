type ('a, 'b) t
val create : (* get *) (unit -> 'a) -> (* state *) 'b -> ('a, 'b) t
val backup : (* x *) ('a, 'b) t -> ('b * int)
val restore : (* x *) ('a, 'b) t -> (* state_to_past_len *) ('b * int) -> unit
val advance : (* x *) ('a, 'b) t -> 'a
val history_length: ('a, 'b) t -> int
val get_state : ('a, 'b) t -> 'b
val set_state : 'b -> ('a, 'b) t -> unit
