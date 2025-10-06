open Fstarcompiler
open Prims
type 'n nbytes = FStar_Bytes.bytes
type tag = Obj.t nbytes
let (sha1 : FStar_Bytes.bytes -> tag) =
  fun uu___ -> failwith "Not yet implemented: FStar.Crypto.sha1"
type hmac_key = Obj.t nbytes
let (hmac_sha1_keygen : unit -> hmac_key) =
  fun uu___ -> failwith "Not yet implemented: FStar.Crypto.hmac_sha1_keygen"
let (hmac_sha1 : hmac_key -> FStar_Bytes.bytes -> tag) =
  fun uu___ ->
    fun uu___1 -> failwith "Not yet implemented: FStar.Crypto.hmac_sha1"
let (hmac_sha1_verify : hmac_key -> FStar_Bytes.bytes -> tag -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        failwith "Not yet implemented: FStar.Crypto.hmac_sha1_verify"
type block = Obj.t nbytes
type cipher = Obj.t nbytes
type aes_key = Obj.t nbytes
type aes_iv = Obj.t nbytes
let (aes_128_keygen : unit -> aes_key) =
  fun uu___ -> failwith "Not yet implemented: FStar.Crypto.aes_128_keygen"
let (aes_128_decrypt : aes_key -> cipher -> block) =
  fun uu___ ->
    fun uu___1 ->
      failwith "Not yet implemented: FStar.Crypto.aes_128_decrypt"
let (aes_128_encrypt : aes_key -> block -> cipher) =
  fun k ->
    fun p -> failwith "Not yet implemented: FStar.Crypto.aes_128_encrypt"
let (aes_128_ivgen : unit -> aes_iv) =
  fun uu___ -> failwith "Not yet implemented: FStar.Crypto.aes_128_ivgen"
let (aes_128_cbc_decrypt :
  aes_key -> aes_iv -> FStar_Bytes.bytes -> FStar_Bytes.bytes) =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        failwith "Not yet implemented: FStar.Crypto.aes_128_cbc_decrypt"
let (aes_128_cbc_encrypt :
  aes_key -> aes_iv -> FStar_Bytes.bytes -> FStar_Bytes.bytes) =
  fun k ->
    fun iv ->
      fun p ->
        failwith "Not yet implemented: FStar.Crypto.aes_128_cbc_encrypt"
type rsa_pkey = {
  modulus: FStar_Bytes.bytes ;
  exponent: FStar_Bytes.bytes }
let (__proj__Mkrsa_pkey__item__modulus : rsa_pkey -> FStar_Bytes.bytes) =
  fun projectee -> match projectee with | { modulus; exponent;_} -> modulus
let (__proj__Mkrsa_pkey__item__exponent : rsa_pkey -> FStar_Bytes.bytes) =
  fun projectee -> match projectee with | { modulus; exponent;_} -> exponent
type rsa_skey = (rsa_pkey * FStar_Bytes.bytes)
let (rsa_keygen : unit -> rsa_skey) =
  fun uu___ -> failwith "Not yet implemented: FStar.Crypto.rsa_keygen"
let (rsa_pk : rsa_skey -> rsa_pkey) =
  fun uu___ -> failwith "Not yet implemented: FStar.Crypto.rsa_pk"
let (rsa_pkcs1_encrypt : rsa_pkey -> FStar_Bytes.bytes -> FStar_Bytes.bytes)
  =
  fun uu___ ->
    fun uu___1 ->
      failwith "Not yet implemented: FStar.Crypto.rsa_pkcs1_encrypt"
let (rsa_pkcs1_decrypt : rsa_skey -> FStar_Bytes.bytes -> FStar_Bytes.bytes)
  =
  fun uu___ ->
    fun uu___1 ->
      failwith "Not yet implemented: FStar.Crypto.rsa_pkcs1_decrypt"
type sigv = FStar_Bytes.bytes
let (rsa_sha1 : rsa_skey -> FStar_Bytes.bytes -> sigv) =
  fun uu___ ->
    fun uu___1 -> failwith "Not yet implemented: FStar.Crypto.rsa_sha1"
let (rsa_sha1_verify : rsa_pkey -> FStar_Bytes.bytes -> sigv -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        failwith "Not yet implemented: FStar.Crypto.rsa_sha1_verify"
