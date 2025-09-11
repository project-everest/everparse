#[macro_use]
extern crate static_assertions;

const_assert!(usize::BITS >= 64);

mod lowstar {
    pub mod ignore {
        pub fn ignore<T>(_: T) {}
    }
}

mod commonabort {
    pub fn abort() -> ! {
        std::process::abort();
    }
}

extern crate ed25519_dalek;

mod ed25519 {
    use ed25519_dalek::ed25519::signature::SignerMut;

    pub fn sign(signature: &mut [u8], private_key: &[u8], msg: &[u8]) {
        signature.copy_from_slice(
            &ed25519_dalek::SigningKey::from_bytes(private_key.try_into().unwrap())
                .sign(msg)
                .to_bytes(),
        );
    }

    pub fn verify(public_key: &[u8], msg: &[u8], signature: &[u8]) -> bool {
        match ed25519_dalek::VerifyingKey::from_bytes(public_key.try_into().unwrap()) {
            Ok(verifying_key) => verifying_key
                .verify_strict(
                    msg,
                    &ed25519_dalek::Signature::from_bytes(signature.try_into().unwrap()),
                )
                .is_ok(),
            Err(_) => false,
        }
    }
}

pub mod cbordetver;
pub mod cbordetveraux;

pub mod commonpulse;
pub mod coseformat;