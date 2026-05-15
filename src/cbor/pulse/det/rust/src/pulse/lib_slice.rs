// Rust glue for the abstract module `Pulse.Lib.Slice` (treated as a model by
// Karamel for Rust extraction).  Pulse's permission discipline guarantees
// that the caller holds full write-permission on the underlying memory at
// the call sites that take `&[T]` and return `&mut [T]`, so the unsafe
// reborrow performed here does not violate Rust's aliasing rules in
// well-typed Pulse code.

/// Reinterpret an immutable slice as a mutable slice.
///
/// This is the Rust counterpart of `Pulse.Lib.Slice.slice_to_arrayptr_intro`.
/// Pulse's typing discipline guarantees that the caller actually owns the
/// underlying memory with full permission (`pts_to s #1.0R v`), so the
/// returned mutable slice does not alias any other live reference.
pub fn slice_to_arrayptr_intro<T>(s: &[T]) -> &mut [T] {
    let ptr = s.as_ptr() as *mut T;
    let len = s.len();
    unsafe { core::slice::from_raw_parts_mut(ptr, len) }
}

/// Take a prefix of a mutable slice; the resulting slice is what Pulse views
/// as the "slice" view of an array pointer with explicit length.
///
/// This is the Rust counterpart of `Pulse.Lib.Slice.arrayptr_to_slice_intro`.
pub fn arrayptr_to_slice_intro<T>(p: &mut [T], len: usize) -> &mut [T] {
    &mut p[..len]
}
