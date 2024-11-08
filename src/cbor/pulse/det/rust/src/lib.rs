#[macro_use]
extern crate static_assertions;

const_assert!(usize::BITS >= 64);

pub mod lowstar {
    pub mod ignore {
        pub fn ignore<T>(_: T) {}
    }
}
pub mod cbordet;

#[cfg(test)] mod test;
