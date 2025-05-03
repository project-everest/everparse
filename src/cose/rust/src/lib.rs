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

mod ed25519 {
    pub fn sign(signature: &mut [u8], private_key: &[u8], msg: &[u8]) {
        std::process::abort();
    }
    
    pub fn verify(public_key: &[u8], msg: &[u8], signature: &[u8]) -> bool {
        std::process::abort()
    }
}

pub mod cbordetver;
pub mod cbordetveraux;

pub mod coseformat;
pub mod commonpulse;
