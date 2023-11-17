//! A module containing the VTable for reference counted pointers.

use crate::erased_ptr::TypeErasedPtr;

/// A shared VTable for both atomic and non-atomic reference counted pointers.
///
/// This allows us to store function pointers to all necessary operations we need to do with
/// reference-counted pointers, while not having to care which type is stored in them.
#[derive(Debug)]
pub(crate) struct RcVTable {
    pub clone: unsafe fn(TypeErasedPtr),
    pub drop: unsafe fn(TypeErasedPtr),
    pub downgrade: unsafe fn(TypeErasedPtr) -> TypeErasedPtr,
    pub strong_count: unsafe fn(TypeErasedPtr) -> usize,
    pub weak_count: unsafe fn(TypeErasedPtr) -> usize,

    pub clone_weak: unsafe fn(TypeErasedPtr),
    pub drop_weak: unsafe fn(TypeErasedPtr),
    pub upgrade_weak: unsafe fn(TypeErasedPtr) -> Option<TypeErasedPtr>,
    pub strong_count_weak: unsafe fn(TypeErasedPtr) -> usize,
    pub weak_count_weak: unsafe fn(TypeErasedPtr) -> usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn debug() {
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn a(_: TypeErasedPtr) {}
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn b(ptr: TypeErasedPtr) -> TypeErasedPtr {
            ptr
        }
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn c(_: TypeErasedPtr) -> usize {
            0
        }
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn d(_: TypeErasedPtr) -> Option<TypeErasedPtr> {
            None
        }

        let vtable = RcVTable {
            clone: a,
            drop: a,
            downgrade: b,
            strong_count: c,
            weak_count: c,
            clone_weak: a,
            drop_weak: a,
            upgrade_weak: d,
            strong_count_weak: c,
            weak_count_weak: c,
        };
        format!("{:?}", vtable);
    }
}
