mod lowstar {
    pub mod ignore {
        pub fn ignore<T>(_: T) {}
    }
}

mod cbornondetveraux;

// Option types extracted by KaRaMeL from CBOR.Pulse.API.Nondet.Rust.Alloc,
// re-exported by the hand-written trusted allocator below.
#[path = "cbornondetalloc.rs"]
mod cbornondetalloctypes;

#[path = "cbornondetallocimpl.rs"]
mod cbornondetalloc;

pub mod cbornondetver;

pub mod cbornondet;
