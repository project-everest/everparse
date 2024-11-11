#[macro_use]
extern crate static_assertions;

const_assert!(usize::BITS >= 64);

mod lowstar {
    pub mod ignore {
        pub fn ignore<T>(_: T) {}
    }
}

pub mod cbordet;
