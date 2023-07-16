use core::{
    marker::Sized,
    mem::{size_of, MaybeUninit},
};

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub(crate) struct TypeErasedPtr(MaybeUninit<[*const (); 2]>);

impl TypeErasedPtr {
    /// Type-erase a possibly-unsized pointer,
    /// only preserving the bit-representation of its pointer.
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
    pub(crate) unsafe fn as_ptr<T: ?Sized>(self) -> *const T {
        core::mem::transmute_copy(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::TypeErasedPtr;
    use alloc::{format, string::String, vec};

    #[test]
    fn sized() {
        let s = String::from("Hello!");
        let ptr = TypeErasedPtr::new(&s);

        let r: &String = unsafe { &*ptr.as_ptr() };
        assert_eq!(r as *const String, &s as *const String);
        assert_eq!(r, &s);
    }

    #[test]
    fn unsized_slice() {
        let boxed_slice = vec![1u8, 2, 3, 4, 5].into_boxed_slice();
        let ptr = TypeErasedPtr::new(&*boxed_slice as *const [u8]);

        let r: &[u8] = unsafe { &*ptr.as_ptr() };
        assert_eq!(r as *const [_], &*boxed_slice as *const [u8]);
        assert_eq!(r, &*boxed_slice);
    }

    #[test]
    fn dyn_ptr() {
        // We want to check that the pointers actually ARE compatible
        #![allow(clippy::vtable_address_comparisons)]

        let debug: &dyn core::fmt::Debug = &"Hello!";
        let ptr = TypeErasedPtr::new(debug as *const dyn core::fmt::Debug);

        let r: &dyn core::fmt::Debug = unsafe { &*ptr.as_ptr() };
        assert_eq!(r as *const _, debug as *const dyn core::fmt::Debug);
        assert_eq!(format!("{:?}", r), "\"Hello!\"");
    }
}
