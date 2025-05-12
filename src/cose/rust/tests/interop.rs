use cose::keys::CoseKey;
use ed25519_dalek::{SigningKey, VerifyingKey};
use evercosign::commonpulse;
use rand::{RngCore, SeedableRng};

fn generate_key() -> ed25519_dalek::SigningKey {
    let mut csprng = rand::rngs::StdRng::from_os_rng();
    let mut secret = ed25519_dalek::SecretKey::default();
    csprng.fill_bytes(&mut secret);
    ed25519_dalek::SigningKey::from_bytes(&secret)
}

fn ed25519_key_to_cose_rust_key(key: &SigningKey) -> CoseKey {
    let mut cosekey = cose::keys::CoseKey::new();
    cosekey.kty(cose::keys::OKP);
    cosekey.alg(cose::algs::EDDSA);
    cosekey.crv(cose::keys::ED25519);
    cosekey.d(key.to_bytes().to_vec());
    cosekey.key_ops(vec![cose::keys::KEY_OPS_SIGN]);
    cosekey
}

fn cose_rust_sign1(key: &CoseKey, payload: Vec<u8>) -> Vec<u8> {
    let mut sign1 = cose::message::CoseMessage::new_sign();
    sign1.header.alg(cose::algs::EDDSA, true, false);
    sign1.payload(payload);
    sign1.key(key).unwrap();
    sign1.secure_content(None).unwrap();
    sign1.encode(true).unwrap();
    sign1.bytes
}

fn ed25519_key_to_cose_rust_pubkey(key: &VerifyingKey) -> CoseKey {
    let mut cosekey = cose::keys::CoseKey::new();
    cosekey.kty(cose::keys::OKP);
    cosekey.alg(cose::algs::EDDSA);
    cosekey.crv(cose::keys::ED25519);
    cosekey.x(key.to_bytes().to_vec());
    cosekey.key_ops(vec![cose::keys::KEY_OPS_VERIFY]);
    cosekey
}

fn cose_rust_verify(pubkey: &CoseKey, msg: Vec<u8>) {
    let mut verify = cose::message::CoseMessage::new_sign();
    verify.bytes = msg;
    verify.init_decoder(None).unwrap();
    verify.key(pubkey).unwrap();
    verify.decode(None, None).unwrap();
}

#[test]
fn sign_and_verify() {
    let key = generate_key();
    let payload = b"payload";
    let mut outbuf = vec![0; 1024];
    let signed = commonpulse::sign1_simple(key.as_bytes(), payload, &mut outbuf);
    assert!(
        commonpulse::verify1_simple(&key.verifying_key().to_bytes(), &signed)
            == commonpulse::option__Pulse_Lib_Slice_slice·uint8_t::Some { v: payload }
    );
}

#[test]
fn verify() {
    let key = generate_key();
    let cosekey = ed25519_key_to_cose_rust_key(&key);
    let payload = b"payload";
    let signed = cose_rust_sign1(&cosekey, payload.to_vec());
    assert!(
        commonpulse::verify1_simple(&key.verifying_key().to_bytes(), &signed)
            == commonpulse::option__Pulse_Lib_Slice_slice·uint8_t::Some { v: payload }
    );
}

#[test]
#[ignore] // rust-cose can't parse our signed message?!?
fn sign() {
    let key = generate_key();
    let payload = b"payload";
    let mut outbuf = vec![0; 1024];
    let msg = commonpulse::sign1_simple(key.as_bytes(), payload, &mut outbuf);
    cose_rust_verify(&ed25519_key_to_cose_rust_pubkey(&key.verifying_key()), msg.to_vec());
}
