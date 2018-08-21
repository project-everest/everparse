type prog = gemstone_t list

and attr = string

and type_t = string

and fieldName = string

and sval = int list

and gemstone_t =
	| Enum of (enum_fields_t list * type_t * attr list)
	| Struct of (type_t * attr list * struct_fields_t list)
	| SelectStruct of (type_t * type_t * (type_t * struct_fields_t list) list)
        | SingleFieldStruct of (type_t * attr list * vector_t)
        | Abstract of (type_t * attr list * int * int)

and vector_t =
	| VectorSimple of (type_t * type_t)
	| VectorSize of (type_t * type_t * int)
	| VectorSymbolic of (type_t * type_t * type_t)
	| VectorRange of (type_t * type_t * (int * int))

and enum_fields_t =
	| EnumFieldSimple of (type_t * int)
	| EnumFieldRange of (type_t * int * int)
	| EnumFieldAnonymous of int

and struct_fields_t =
	| StructFieldSimple of (vector_t * sval option)
	| StructFieldSelect of (type_t * select_fields_t list * type_t)

and select_fields_t =
	| SelectField of (type_t * type_t)
