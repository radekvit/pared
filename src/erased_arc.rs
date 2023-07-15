use std::{
    marker::PhantomData,
    sync::{Arc, Weak},
};

use crate::erased_ptr::TypeErasedPtr;

pub struct TypeErasedArc {
    ptr: TypeErasedPtr,
    lifecycle: &'static TypeErasedLifecycle,
}

impl TypeErasedArc {
    pub(crate) fn new<T: ?Sized>(arc: Arc<T>) -> Self {
        Self {
            ptr: TypeErasedPtr::new(Arc::into_raw(arc)),
            lifecycle: &ArcErased::<T>::LIFECYCLE,
        }
    }

    pub(crate) fn downgrade(&self) -> TypeErasedWeak {
        TypeErasedWeak {
            ptr: unsafe { (self.lifecycle.downgrade)(self.ptr) },
            lifecycle: self.lifecycle,
        }
    }

    pub(crate) fn strong_count(&self) -> usize {
        unsafe { (self.lifecycle.strong_count)(self.ptr) }
    }

    pub(crate) fn weak_count(&self) -> usize {
        unsafe { (self.lifecycle.weak_count)(self.ptr) }
    }
}

impl Clone for TypeErasedArc {
    fn clone(&self) -> Self {
        unsafe {
            (self.lifecycle.clone)(self.ptr);
        }
        Self { ..*self }
    }
}

impl Drop for TypeErasedArc {
    fn drop(&mut self) {
        unsafe {
            (self.lifecycle.drop)(self.ptr);
        }
    }
}

pub(crate) struct TypeErasedWeak {
    ptr: TypeErasedPtr,
    lifecycle: &'static TypeErasedLifecycle,
}

impl TypeErasedWeak {
    pub(crate) fn upgrade(&self) -> Option<TypeErasedArc> {
        Some(TypeErasedArc {
            ptr: unsafe { (self.lifecycle.upgrade_weak)(self.ptr) }?,
            lifecycle: self.lifecycle,
        })
    }

    pub(crate) fn strong_count(&self) -> usize {
        unsafe { (self.lifecycle.strong_count_weak)(self.ptr) }
    }

    pub(crate) fn weak_count(&self) -> usize {
        unsafe { (self.lifecycle.weak_count_weak)(self.ptr) }
    }
}

impl Clone for TypeErasedWeak {
    fn clone(&self) -> Self {
        unsafe {
            (self.lifecycle.clone_weak)(self.ptr);
        }
        Self { ..*self }
    }
}

impl Drop for TypeErasedWeak {
    fn drop(&mut self) {
        unsafe {
            (self.lifecycle.drop_weak)(self.ptr);
        }
    }
}

pub(crate) struct TypeErasedLifecycle {
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

pub(crate) struct ArcErased<T: ?Sized>(PhantomData<*const T>);

impl<T: ?Sized> ArcErased<T> {
    pub(crate) const LIFECYCLE: TypeErasedLifecycle = TypeErasedLifecycle {
        clone: Self::clone,
        drop: Self::drop,
        downgrade: Self::downgrade,
        strong_count: Self::strong_count,
        weak_count: Self::weak_count,
        clone_weak: Self::clone_weak,
        drop_weak: Self::drop_weak,
        upgrade_weak: Self::upgrade_weak,
        strong_count_weak: Self::strong_count_weak,
        weak_count_weak: Self::weak_count_weak,
    };

    pub(crate) unsafe fn clone(ptr: TypeErasedPtr) {
        let arc: *const T = ptr.as_ptr();
        Arc::increment_strong_count(arc);
    }

    pub(crate) unsafe fn drop(ptr: TypeErasedPtr) {
        Self::as_arc(ptr);
    }

    pub(crate) unsafe fn downgrade(ptr: TypeErasedPtr) -> TypeErasedPtr {
        let arc = Self::as_arc(ptr);
        let weak = Arc::downgrade(&arc);
        std::mem::forget(arc);
        TypeErasedPtr::new(Weak::into_raw(weak))
    }

    pub(crate) unsafe fn strong_count(ptr: TypeErasedPtr) -> usize {
        let arc = Self::as_arc(ptr);
        let count = Arc::strong_count(&arc);
        std::mem::forget(arc);
        count
    }
    pub(crate) unsafe fn weak_count(ptr: TypeErasedPtr) -> usize {
        let arc = Self::as_arc(ptr);
        let count = Arc::weak_count(&arc);
        std::mem::forget(arc);
        count
    }
    pub(crate) unsafe fn clone_weak(ptr: TypeErasedPtr) {
        let weak = Self::as_weak(ptr);
        std::mem::forget(weak.clone());
        std::mem::forget(weak);
    }
    pub(crate) unsafe fn drop_weak(ptr: TypeErasedPtr) {
        let weak = Self::as_weak(ptr);
        std::mem::drop(weak);
    }
    pub(crate) unsafe fn upgrade_weak(ptr: TypeErasedPtr) -> Option<TypeErasedPtr> {
        let weak = Self::as_weak(ptr);
        let arc = weak.upgrade();
        std::mem::forget(weak);
        arc.map(|arc| TypeErasedPtr::new(Arc::into_raw(arc)))
    }
    pub(crate) unsafe fn strong_count_weak(ptr: TypeErasedPtr) -> usize {
        let weak = Self::as_weak(ptr);
        let count = Weak::strong_count(&weak);
        std::mem::forget(weak);
        count
    }
    pub(crate) unsafe fn weak_count_weak(ptr: TypeErasedPtr) -> usize {
        let weak = Self::as_weak(ptr);
        let count = Weak::weak_count(&weak);
        std::mem::forget(weak);
        count
    }

    pub(crate) unsafe fn as_arc(ptr: TypeErasedPtr) -> Arc<T> {
        Arc::from_raw(ptr.as_ptr())
    }

    pub(crate) unsafe fn as_weak(ptr: TypeErasedPtr) -> Weak<T> {
        Weak::from_raw(ptr.as_ptr())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erased_arc_drop() {
        static mut DROPPED_COUNT: usize = 0;
        struct Drops;

        impl Drop for Drops {
            fn drop(&mut self) {
                // SAFETY: we're single-threaded and never hold a reference to this
                unsafe {
                    DROPPED_COUNT += 1;
                }
            }
        }
        let arc = Arc::new(Drops);
        let erased = TypeErasedArc::new(arc.clone());
        // The variable shouldn't drop after we drop the original Arc
        std::mem::drop(arc);
        assert_eq!(unsafe { DROPPED_COUNT }, 0);

        // The variable shouldn't drop after we drop a second erased instance
        let erased2 = erased.clone();
        std::mem::drop(erased2);
        assert_eq!(unsafe { DROPPED_COUNT }, 0);

        // The variable should drop after we drop the last instance
        // with the correct Drop implementation called
        std::mem::drop(erased);
        assert_eq!(unsafe { DROPPED_COUNT }, 1);
    }
}
