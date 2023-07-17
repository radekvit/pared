use alloc::rc::{Rc, Weak};
use core::{
    clone::Clone,
    marker::{PhantomData, Sized},
    mem::ManuallyDrop,
    ops::Drop,
    option::{Option, Option::Some},
};

use crate::erased_ptr::TypeErasedPtr;

pub struct TypeErasedRc {
    ptr: TypeErasedPtr,
    lifecycle: &'static TypeErasedLifecycle,
    _phantom: PhantomData<*mut ()>,
}

impl TypeErasedRc {
    #[inline]
    pub(crate) fn new<T: ?Sized>(arc: Rc<T>) -> Self {
        Self {
            ptr: TypeErasedPtr::new(Rc::into_raw(arc)),
            lifecycle: &RcErased::<T>::LIFECYCLE,
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn downgrade(&self) -> TypeErasedWeak {
        TypeErasedWeak {
            // SAFETY: downgrade is guaranteed to return an erased pointer to Weak<T>
            ptr: unsafe { (self.lifecycle.downgrade)(self.ptr) },
            lifecycle: self.lifecycle,
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn strong_count(&self) -> usize {
        // SAFETY: once set in TypeErasedRc::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.strong_count)(self.ptr) }
    }

    #[inline]
    pub(crate) fn weak_count(&self) -> usize {
        // SAFETY: once set in TypeErasedRc::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.weak_count)(self.ptr) }
    }
}

impl Clone for TypeErasedRc {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: once set in TypeErasedRc::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.clone)(self.ptr) }
        Self { ..*self }
    }
}

impl Drop for TypeErasedRc {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: once set in TypeErasedRc::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.drop)(self.ptr) }
    }
}

pub(crate) struct TypeErasedWeak {
    ptr: TypeErasedPtr,
    lifecycle: &'static TypeErasedLifecycle,
    _phantom: PhantomData<*mut ()>,
}

impl TypeErasedWeak {
    #[inline]
    pub(crate) fn upgrade(&self) -> Option<TypeErasedRc> {
        Some(TypeErasedRc {
            // SAFETY: upgrade_weak is guaranteed to return an erased pointer to Rc<T>
            ptr: unsafe { (self.lifecycle.upgrade_weak)(self.ptr) }?,
            lifecycle: self.lifecycle,
            _phantom: PhantomData,
        })
    }

    #[inline]
    pub(crate) fn strong_count(&self) -> usize {
        // SAFETY: once set in TypeErasedWeak::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.strong_count_weak)(self.ptr) }
    }

    #[inline]
    pub(crate) fn weak_count(&self) -> usize {
        // SAFETY: once set in TypeErasedWeak::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.weak_count_weak)(self.ptr) }
    }
}

impl Clone for TypeErasedWeak {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: once set in TypeErasedWeak::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.clone_weak)(self.ptr) }
        Self { ..*self }
    }
}

impl Drop for TypeErasedWeak {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: once set in TypeErasedWeak::new, self.lifecycle is never modified,
        // which guarantees that self.lifecycle and self.ptr match
        unsafe { (self.lifecycle.drop_weak)(self.ptr) }
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

pub(crate) struct RcErased<T: ?Sized>(PhantomData<*const T>);

impl<T: ?Sized> RcErased<T> {
    // A "vtable" for Rc<T> and rc::Weak<T> where T: ?Sized
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

    // Must be called with an erased pointer to Rc<T>
    pub(crate) unsafe fn clone(ptr: TypeErasedPtr) {
        let arc: *const T = ptr.as_ptr();
        Rc::increment_strong_count(arc);
    }

    // Must be called with an erased pointer to Rc<T>
    pub(crate) unsafe fn drop(ptr: TypeErasedPtr) {
        let rc: Rc<T> = Rc::from_raw(ptr.as_ptr());
        core::mem::drop(rc);
    }

    // Must be called with an erased pointer to Rc<T>
    pub(crate) unsafe fn downgrade(ptr: TypeErasedPtr) -> TypeErasedPtr {
        let arc = Self::as_manually_drop_rc(ptr);
        let weak = Rc::downgrade(&arc);
        TypeErasedPtr::new(Weak::into_raw(weak))
    }

    // Must be called with an erased pointer to Rc<T>
    pub(crate) unsafe fn strong_count(ptr: TypeErasedPtr) -> usize {
        let arc = Self::as_manually_drop_rc(ptr);
        Rc::strong_count(&arc)
    }
    // Must be called with an erased pointer to Rc<T>
    pub(crate) unsafe fn weak_count(ptr: TypeErasedPtr) -> usize {
        let arc = Self::as_manually_drop_rc(ptr);
        Rc::weak_count(&arc)
    }
    // Must be called with an erased pointer to rc::Weak<T>
    pub(crate) unsafe fn clone_weak(ptr: TypeErasedPtr) {
        let weak = Self::as_manually_drop_weak(ptr);
        let _cloned = weak.clone();
    }
    // Must be called with an erased pointer to rc::Weak<T>
    pub(crate) unsafe fn drop_weak(ptr: TypeErasedPtr) {
        let weak: Weak<T> = Weak::from_raw(ptr.as_ptr());
        core::mem::drop(weak);
    }
    // Must be called with an erased pointer to rc::Weak<T>
    pub(crate) unsafe fn upgrade_weak(ptr: TypeErasedPtr) -> Option<TypeErasedPtr> {
        let weak = Self::as_manually_drop_weak(ptr);
        let arc = weak.upgrade();
        arc.map(|arc| TypeErasedPtr::new(Rc::into_raw(arc)))
    }
    // Must be called with an erased pointer to rc::Weak<T>
    pub(crate) unsafe fn strong_count_weak(ptr: TypeErasedPtr) -> usize {
        let weak = Self::as_manually_drop_weak(ptr);
        Weak::strong_count(&weak)
    }
    // Must be called with an erased pointer to rc::Weak<T>
    pub(crate) unsafe fn weak_count_weak(ptr: TypeErasedPtr) -> usize {
        let weak = Self::as_manually_drop_weak(ptr);
        Weak::weak_count(&weak)
    }

    // Must be called with an erased pointer to rc::Weak<T>
    #[inline]
    unsafe fn as_manually_drop_rc(ptr: TypeErasedPtr) -> ManuallyDrop<Rc<T>> {
        ManuallyDrop::new(Rc::from_raw(ptr.as_ptr()))
    }

    #[inline]
    unsafe fn as_manually_drop_weak(ptr: TypeErasedPtr) -> ManuallyDrop<Weak<T>> {
        ManuallyDrop::new(Weak::from_raw(ptr.as_ptr()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erased_arc_drops_object_when_last_instance_drops() {
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
        let arc = Rc::new(Drops);
        let erased = TypeErasedRc::new(arc.clone());
        // The variable shouldn't drop after we drop the original Arc
        core::mem::drop(arc);
        assert_eq!(unsafe { DROPPED_COUNT }, 0);

        // The variable shouldn't drop after we drop a second erased instance
        let erased2 = erased.clone();
        core::mem::drop(erased2);
        assert_eq!(unsafe { DROPPED_COUNT }, 0);

        // The variable should drop after we drop the last instance
        // with the correct Drop implementation called
        core::mem::drop(erased);
        assert_eq!(unsafe { DROPPED_COUNT }, 1);
    }

    #[test]
    fn erased_arc_drops_object_when_last_instance_drops_with_weak() {
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
        let arc = Rc::new(Drops);
        let erased = TypeErasedRc::new(arc);
        let _weak = erased.downgrade();
        assert_eq!(unsafe { DROPPED_COUNT }, 0);

        // The variable shouldn't drop after we drop a second erased instance
        let erased2 = erased.clone();
        core::mem::drop(erased2);
        assert_eq!(unsafe { DROPPED_COUNT }, 0);

        // The variable should drop after we drop the last instance
        // with the correct Drop implementation called
        core::mem::drop(erased);
        assert_eq!(unsafe { DROPPED_COUNT }, 1);
    }

    #[test]
    fn erased_arc_strong_count_tracks_instances() {
        let arc = Rc::new(42);
        let erased = TypeErasedRc::new(arc);
        assert_eq!(erased.strong_count(), 1);

        let erased2 = erased.clone();
        assert_eq!(erased.strong_count(), 2);
        assert_eq!(erased2.strong_count(), 2);

        let weak = erased.downgrade();
        assert_eq!(erased.strong_count(), 2);
        assert_eq!(erased2.strong_count(), 2);
        assert_eq!(weak.strong_count(), 2);

        core::mem::drop(erased);
        core::mem::drop(weak);
        assert_eq!(erased2.strong_count(), 1);
    }

    #[test]
    fn erased_arc_weak_count() {
        let arc = Rc::new(42);
        let erased = TypeErasedRc::new(arc);
        assert_eq!(erased.weak_count(), 0);

        let erased2 = erased.clone();
        assert_eq!(erased.weak_count(), 0);
        assert_eq!(erased2.weak_count(), 0);

        core::mem::drop(erased);
        assert_eq!(erased2.weak_count(), 0);

        let weak = erased2.downgrade();
        assert_eq!(erased2.weak_count(), 1);
        assert_eq!(weak.weak_count(), 1);

        let weak2 = weak.clone();
        assert_eq!(weak.weak_count(), 2);
        assert_eq!(weak2.weak_count(), 2);

        core::mem::drop(erased2);
        // weak_count returns 0 when there are no remaning Arcs
        assert_eq!(weak.weak_count(), 0);
    }

    #[test]
    fn weak_can_upgrade_when_there_are_instances() {
        let arc = Rc::new(42);
        let erased = TypeErasedRc::new(arc);
        let weak = erased.downgrade();

        let upgraded = weak.upgrade().unwrap();
        core::mem::drop(erased);
        assert_eq!(upgraded.strong_count(), 1);

        core::mem::drop(upgraded);

        let upgraded = weak.upgrade();
        assert!(matches!(upgraded, None));
    }
}
