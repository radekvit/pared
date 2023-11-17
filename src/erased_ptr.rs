use core::{
    assert,
    clone::Clone,
    marker::{Copy, Sized},
    mem::{size_of, MaybeUninit},
};

/// A type-erased, potentially fat pointer to anything.
///
/// This type will only work with the assumption that all pointers are at most 2 pointers.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct TypeErasedPtr(MaybeUninit<[*const (); 2]>);

impl core::fmt::Debug for TypeErasedPtr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("TypeErasedPtr").field(&self.0).finish()
    }
}

impl TypeErasedPtr {
    /// Type-erase a possibly-unsized pointer,
    /// only preserving the bit-representation of its pointer.
    #[inline]
    pub(crate) fn new<T: ?Sized>(ptr: *const T) -> Self {
        let mut res = Self(MaybeUninit::zeroed());

        let len = size_of::<*const T>();

        assert!(len <= size_of::<[*const (); 2]>());

        // SAFETY: The target is valid for at least `len` bytes, and has no
        // requirements on the value.
        // We asserted that our pointer fits into this representation.
        unsafe {
            let ptr_val = (&ptr) as *const *const T as *const u8;
            let target = res.0.as_mut_ptr() as *mut u8;
            core::ptr::copy_nonoverlapping(ptr_val, target, len);
        }
        res
    }

    /// Obtain the original pointer from the type-erased representation.
    ///
    /// # Safety
    /// This can only be called with `Self` that has been created from the exact same `T`.
    #[inline]
    pub(crate) unsafe fn as_ptr<T: ?Sized>(self) -> *const T {
        core::mem::transmute_copy(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::TypeErasedPtr;
    use alloc::{format, string::String, vec};

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn sized() {
        let s = String::from("Hello!");
        let ptr = TypeErasedPtr::new(&s);

        let r: &String = unsafe { &*ptr.as_ptr() };
        assert_eq!(r as *const String, &s as *const String);
        assert_eq!(r, &s);
    }

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn unsized_slice() {
        let boxed_slice = vec![1u8, 2, 3, 4, 5].into_boxed_slice();
        let ptr = TypeErasedPtr::new(&*boxed_slice as *const [u8]);

        let r: &[u8] = unsafe { &*ptr.as_ptr() };
        assert_eq!(r as *const [_], &*boxed_slice as *const [u8]);
        assert_eq!(r, &*boxed_slice);
    }

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn dyn_ptr() {
        // We want to check that the pointers actually ARE compatible
        #![allow(clippy::vtable_address_comparisons)]

        let debug: &dyn core::fmt::Debug = &"Hello!";
        let ptr = TypeErasedPtr::new(debug as *const dyn core::fmt::Debug);

        let r: &dyn core::fmt::Debug = unsafe { &*ptr.as_ptr() };
        assert_eq!(r as *const _, debug as *const dyn core::fmt::Debug);
        assert_eq!(format!("{:?}", r), "\"Hello!\"");
    }

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone() {
        let ptr = TypeErasedPtr::new(&1);
        #[allow(clippy::clone_on_copy)]
        let _ = ptr.clone();
    }

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn debug() {
        let ptr = TypeErasedPtr::new(&1);
        format!("{:?}", ptr);
    }
}
