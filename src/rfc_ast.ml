type prog = gemstone_t list

and attr = string
and typ = string
and field = string
and sval = int list

and gemstone_t =
	| Enum of attr list * enum_field_t list * typ
	| Struct of attr list * struct_field_t list * typ
	| Typedef of struct_field_t

and type_t =
  | TypeSimple of typ
  | TypeSelect of field * (typ * typ) list * typ option

and vector_t =
	| VectorNone
	| VectorFixed of int
	| VectorFixedCount of int
	| VectorSymbolic of field
	| VectorRange of int * int * typ option
	| VectorCount of int * int * typ option
	| VectorVldata of typ

and enum_field_t =
	| EnumFieldSimple of (typ * int)
	| EnumFieldRange of (typ * int * int)
	| EnumFieldAnonymous of int

and struct_field_t = attr list * type_t * field * vector_t * sval option
