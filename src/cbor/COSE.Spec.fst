module COSE.Spec
module Cddl = CDDL.Spec
module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8

(* RFC 9052 *)

// Section 9: COSE uses CBOR (RFC 8949) Section 4.2.1
let data_item_order = Cbor.deterministically_encoded_cbor_map_key_order

// Section 1.5
let label : Cddl.typ = Cddl.t_int `Cddl.t_choice` Cddl.tstr
let values : Cddl.typ = Cddl.any

// Table 1
[@@CMacro]
let tag_cose_sign = 98uL
[@@CMacro]
let tag_cose_sign1 = 18uL
[@@CMacro]
let tag_cose_encrypt = 96uL
[@@CMacro]
let tag_cose_encrypt0 = 16uL
[@@CMacro]
let tag_cose_mac = 97uL
[@@CMacro]
let tag_cose_mac0 = 17uL

// Table 2
[@@CMacro]
let tag_cose_key = 101uL
[@@CMacro]
let tag_cose_key_set = 102uL

// Section 3.1

[@@CMacro]
let h_alg = 1uL
[@@CMacro]
let h_crit = 2uL
[@@CMacro]
let h_content_type = 3uL
[@@CMacro]
let h_kid = 4uL
[@@CMacro]
let h_iv = 5uL
[@@CMacro]
let h_partial_iv = 6uL

let generic_headers (g: Cddl.map_group None) : Cddl.map_group None =
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal h_alg `Cddl.MapGroupEntry` (Cddl.t_int `Cddl.t_choice` Cddl.tstr)) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal h_crit `Cddl.MapGroupEntry` Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item label))) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal h_content_type `Cddl.MapGroupEntry` (Cddl.tstr `Cddl.t_choice` Cddl.t_int)) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal h_kid `Cddl.MapGroupEntry` Cddl.bstr) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal h_iv `Cddl.t_choice` Cddl.t_uint_literal h_partial_iv `Cddl.MapGroupEntry` Cddl.bstr) false (
  g
)))))

// Section 3

let header_map : Cddl.typ = Cddl.t_map (
  (generic_headers (
    Cddl.map_group_cons_zero_or_more (label `Cddl.MapGroupEntry` values) false
      Cddl.map_group_empty
  ))
)

let empty_or_serialized_map : Cddl.typ =
  Cddl.bstr_cbor data_item_order header_map `Cddl.t_choice`
  Cddl.str_size Cbor.major_type_byte_string 0

let headers #b : Cddl.array_group3 b =
  Cddl.array_group3_item (* protected: *) (Cddl.coerce_to_bounded_typ _ empty_or_serialized_map) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* unprotected: *) (Cddl.coerce_to_bounded_typ _ header_map)

// Section 4.1

let cose_signature : Cddl.typ = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* signature *) Cddl.bstr
)

let cose_sign : Cddl.typ = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* payload *) (Cddl.bstr `Cddl.t_choice` Cddl.t_nil) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* signatures *) (Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item cose_signature)))
)

let cose_sign_tagged = Cddl.t_tag tag_cose_sign ( cose_sign)

// Section 4.2

let cose_sign1 : Cddl.typ = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* payload *) (Cddl.bstr `Cddl.t_choice` Cddl.t_nil) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* signature *) Cddl.bstr
)

let cose_sign1_tagged = Cddl.t_tag tag_cose_sign1 ( cose_sign1)

// Section 4.4

[@@noextract_to "krml"]
assume val s_Signature : Cddl.string64 // "Signature"

[@@noextract_to "krml"]
assume val s_Signature1 : Cddl.string64 // "Signature1"

let sig_structure = Cddl.t_array3 (
  Cddl.array_group3_item (* context *) (Cddl.name_as_text_string s_Signature `Cddl.t_choice` Cddl.name_as_text_string s_Signature1) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* body_protected *) empty_or_serialized_map `Cddl.array_group3_concat`
  Cddl.array_group3_zero_or_one (Cddl.array_group3_item (* sign_protected *) empty_or_serialized_map) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* external_aad *) Cddl.bstr `Cddl.array_group3_concat`
  Cddl.array_group3_item (* payload *) Cddl.bstr
)

// Section 5.1

let cose_recipient = Cddl.t_array3_rec (fun b cose_recipient ->
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* ciphertext *) (Cddl.coerce_to_bounded_typ _ (Cddl.bstr `Cddl.t_choice` Cddl.t_nil)) `Cddl.array_group3_concat`
  Cddl.array_group3_zero_or_one (Cddl.array_group3_item (* recipients *) (Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item cose_recipient))))
)

let cose_encrypt = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* ciphertext *) (Cddl.bstr `Cddl.t_choice` Cddl.t_nil) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* recipients *) (Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item cose_recipient)))
)

let cose_encrypt_tagged = Cddl.t_tag tag_cose_encrypt ( cose_encrypt)

// Section 5.2

let cose_encrypt0 = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* ciphertext *) (Cddl.bstr `Cddl.t_choice` Cddl.t_nil)
)

let cose_encrypt0_tagged = Cddl.t_tag tag_cose_encrypt0 ( cose_encrypt0)

// Section 5.3

[@@noextract_to "krml"]
assume val s_Encrypt: Cddl.string64 // "Encrypt"

[@@noextract_to "krml"]
assume val s_Encrypt0: Cddl.string64 // "Encrypt0"

[@@noextract_to "krml"]
assume val s_Enc_Recipient: Cddl.string64 // "Enc_Recipient"

[@@noextract_to "krml"]
assume val s_Mac_Recipient: Cddl.string64 // "Mac_Recipient"

[@@noextract_to "krml"]
assume val s_Rec_Recipient: Cddl.string64 // "Rec_Recipient"

let enc_structure = Cddl.t_array3 (
  Cddl.array_group3_item (* context *) (Cddl.name_as_text_string s_Encrypt `Cddl.t_choice` Cddl.name_as_text_string s_Encrypt0 `Cddl.t_choice` Cddl.name_as_text_string s_Enc_Recipient `Cddl.t_choice` Cddl.name_as_text_string s_Mac_Recipient `Cddl.t_choice` Cddl.name_as_text_string s_Rec_Recipient) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* protected *) empty_or_serialized_map `Cddl.array_group3_concat`
  Cddl.array_group3_item (* external_aad *) Cddl.bstr
)

// Section 6.1

let cose_mac = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* payload *) (Cddl.bstr `Cddl.t_choice` Cddl.t_nil) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* tag *) Cddl.bstr `Cddl.array_group3_concat`
  Cddl.array_group3_item (* recipients *) (Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item cose_recipient)))
)

let cose_mac_tagged = Cddl.t_tag tag_cose_mac ( cose_mac)

// Section 6.2

let cose_mac0 = Cddl.t_array3 (
  headers `Cddl.array_group3_concat`
  Cddl.array_group3_item (* payload *) (Cddl.bstr `Cddl.t_choice` Cddl.t_nil) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* tag *) Cddl.bstr
)

let cose_mac0_tagged = Cddl.t_tag tag_cose_mac0 ( cose_mac0)

// Section 6.3

[@@noextract_to "krml"]
assume val s_MAC: Cddl.string64 // "MAC"

[@@noextract_to "krml"]
assume val s_MAC0: Cddl.string64 // "MAC0"

let mac_structure = Cddl.t_array3 (
  Cddl.array_group3_item (* context *) (Cddl.name_as_text_string s_MAC `Cddl.t_choice` Cddl.name_as_text_string s_MAC0) `Cddl.array_group3_concat`
  Cddl.array_group3_item (* protected *) empty_or_serialized_map `Cddl.array_group3_concat`
  Cddl.array_group3_item (* external_aad *) Cddl.bstr `Cddl.array_group3_concat`
  Cddl.array_group3_item (* payload *) Cddl.bstr
)

// Section 7.1, Table 4
[@@CMacro]
let k_kty = 1uL
[@@CMacro]
let k_kid = 2uL
[@@CMacro]
let k_alg = 3uL
[@@CMacro]
let k_key_ops = 4uL
[@@CMacro]
let k_base_iv = 5uL

// Section 7

let cose_key = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal k_kty `Cddl.MapGroupEntry` (Cddl.tstr `Cddl.t_choice` Cddl.t_int)) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal k_kid `Cddl.MapGroupEntry` Cddl.bstr) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal k_alg `Cddl.MapGroupEntry` (Cddl.tstr `Cddl.t_choice` Cddl.t_int)) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal k_key_ops `Cddl.MapGroupEntry` Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item (Cddl.tstr `Cddl.t_choice` Cddl.t_int)))) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal k_base_iv `Cddl.MapGroupEntry` Cddl.bstr) false (
  Cddl.map_group_cons_zero_or_more (label `Cddl.MapGroupEntry` values) false (
  Cddl.map_group_empty
)))))))

let cose_key_set = Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item cose_key))

// Section 2

let cose_untagged_message =
  cose_sign `Cddl.t_choice`
  cose_sign1 `Cddl.t_choice`
  cose_encrypt `Cddl.t_choice`
  cose_encrypt0 `Cddl.t_choice`
  cose_mac `Cddl.t_choice`
  cose_mac0

let cose_tagged_message =
  cose_sign_tagged `Cddl.t_choice`
  cose_sign1_tagged `Cddl.t_choice`
  cose_encrypt_tagged `Cddl.t_choice`
  cose_encrypt0_tagged `Cddl.t_choice`
  cose_mac_tagged `Cddl.t_choice`
  cose_mac0_tagged

let cose_messages = cose_untagged_message `Cddl.t_choice` cose_tagged_message
