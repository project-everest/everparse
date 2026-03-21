open Fstarcompiler
open Prims
type 'n nbytes = FStar_Bytes.bytes
type tag = Obj.t nbytes
let sha1 (uu___ : FStar_Bytes.bytes) : tag=
  failwith "Not yet implemented: FStar.Crypto.sha1"
type hmac_key = Obj.t nbytes
let hmac_sha1_keygen (uu___ : unit) : hmac_key=
  failwith "Not yet implemented: FStar.Crypto.hmac_sha1_keygen"
let hmac_sha1 (uu___ : hmac_key) (uu___1 : FStar_Bytes.bytes) : tag=
  failwith "Not yet implemented: FStar.Crypto.hmac_sha1"
let hmac_sha1_verify (uu___ : hmac_key) (uu___1 : FStar_Bytes.bytes)
  (uu___2 : tag) : Prims.bool=
  failwith "Not yet implemented: FStar.Crypto.hmac_sha1_verify"
type block = Obj.t nbytes
type cipher = Obj.t nbytes
type aes_key = Obj.t nbytes
type aes_iv = Obj.t nbytes
let aes_128_keygen (uu___ : unit) : aes_key=
  failwith "Not yet implemented: FStar.Crypto.aes_128_keygen"
let aes_128_decrypt (uu___ : aes_key) (uu___1 : cipher) : block=
  failwith "Not yet implemented: FStar.Crypto.aes_128_decrypt"
let aes_128_encrypt (k : aes_key) (p : block) : cipher=
  failwith "Not yet implemented: FStar.Crypto.aes_128_encrypt"
let aes_128_ivgen (uu___ : unit) : aes_iv=
  failwith "Not yet implemented: FStar.Crypto.aes_128_ivgen"
let aes_128_cbc_decrypt (uu___ : aes_key) (uu___1 : aes_iv)
  (uu___2 : FStar_Bytes.bytes) : FStar_Bytes.bytes=
  failwith "Not yet implemented: FStar.Crypto.aes_128_cbc_decrypt"
let aes_128_cbc_encrypt (k : aes_key) (iv : aes_iv) (p : FStar_Bytes.bytes) :
  FStar_Bytes.bytes=
  failwith "Not yet implemented: FStar.Crypto.aes_128_cbc_encrypt"
type rsa_pkey = {
  modulus: FStar_Bytes.bytes ;
  exponent: FStar_Bytes.bytes }
let __proj__Mkrsa_pkey__item__modulus (projectee : rsa_pkey) :
  FStar_Bytes.bytes= match projectee with | { modulus; exponent;_} -> modulus
let __proj__Mkrsa_pkey__item__exponent (projectee : rsa_pkey) :
  FStar_Bytes.bytes=
  match projectee with | { modulus; exponent;_} -> exponent
type rsa_skey = (rsa_pkey * FStar_Bytes.bytes)
let rsa_keygen (uu___ : unit) : rsa_skey=
  failwith "Not yet implemented: FStar.Crypto.rsa_keygen"
let rsa_pk (uu___ : rsa_skey) : rsa_pkey=
  failwith "Not yet implemented: FStar.Crypto.rsa_pk"
let rsa_pkcs1_encrypt (uu___ : rsa_pkey) (uu___1 : FStar_Bytes.bytes) :
  FStar_Bytes.bytes=
  failwith "Not yet implemented: FStar.Crypto.rsa_pkcs1_encrypt"
let rsa_pkcs1_decrypt (uu___ : rsa_skey) (uu___1 : FStar_Bytes.bytes) :
  FStar_Bytes.bytes=
  failwith "Not yet implemented: FStar.Crypto.rsa_pkcs1_decrypt"
type sigv = FStar_Bytes.bytes
let rsa_sha1 (uu___ : rsa_skey) (uu___1 : FStar_Bytes.bytes) : sigv=
  failwith "Not yet implemented: FStar.Crypto.rsa_sha1"
let rsa_sha1_verify (uu___ : rsa_pkey) (uu___1 : FStar_Bytes.bytes)
  (uu___2 : sigv) : Prims.bool=
  failwith "Not yet implemented: FStar.Crypto.rsa_sha1_verify"
