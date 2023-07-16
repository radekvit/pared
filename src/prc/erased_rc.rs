use alloc::rc::{Rc, Weak};
use core::marker::PhantomData;
use core::option::{Option, Option::Some};

use crate::erased_ptr::TypeErasedPtr;

pub struct TypeErasedRc {
    ptr: TypeErasedPtr,
    lifecycle: &'static TypeErasedLifecycle,
    _phantom: PhantomData<*mut ()>,
}

impl TypeErasedRc {
    pub(crate) fn new<T: ?Sized>(arc: Rc<T>) -> Self {
        Self {
            ptr: TypeErasedPtr::new(Rc::into_raw(arc)),
            lifecycle: &RcErased::<T>::LIFECYCLE,
            _phantom: PhantomData,
        }
    }

    pub(crate) fn downgrade(&self) -> TypeErasedWeak {
        TypeErasedWeak {
            ptr: unsafe { (self.lifecycle.downgrade)(self.ptr) },
            lifecycle: self.lifecycle,
            _phantom: PhantomData,
        }
    }

    pub(crate) fn strong_count(&self) -> usize {
        unsafe { (self.lifecycle.strong_count)(self.ptr) }
    }

    pub(crate) fn weak_count(&self) -> usize {
        unsafe { (self.lifecycle.weak_count)(self.ptr) }
    }
}

impl Clone for TypeErasedRc {
    fn clone(&self) -> Self {
        unsafe {
            (self.lifecycle.clone)(self.ptr);
        }
        Self { ..*self }
    }
}

impl Drop for TypeErasedRc {
    fn drop(&mut self) {
        unsafe {
            (self.lifecycle.drop)(self.ptr);
        }
    }
}

pub(crate) struct TypeErasedWeak {
    ptr: TypeErasedPtr,
    lifecycle: &'static TypeErasedLifecycle,
    _phantom: PhantomData<*mut ()>,
}

impl TypeErasedWeak {
    pub(crate) fn upgrade(&self) -> Option<TypeErasedRc> {
        Some(TypeErasedRc {
            ptr: unsafe { (self.lifecycle.upgrade_weak)(self.ptr) }?,
            lifecycle: self.lifecycle,
            _phantom: PhantomData,
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

pub(crate) struct RcErased<T: ?Sized>(PhantomData<*const T>);

impl<T: ?Sized> RcErased<T> {
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
        Rc::increment_strong_count(arc);
    }

    pub(crate) unsafe fn drop(ptr: TypeErasedPtr) {
        Self::as_arc(ptr);
    }

    pub(crate) unsafe fn downgrade(ptr: TypeErasedPtr) -> TypeErasedPtr {
        let arc = Self::as_arc(ptr);
        let weak = Rc::downgrade(&arc);
        core::mem::forget(arc);
        TypeErasedPtr::new(Weak::into_raw(weak))
    }

    pub(crate) unsafe fn strong_count(ptr: TypeErasedPtr) -> usize {
        let arc = Self::as_arc(ptr);
        let count = Rc::strong_count(&arc);
        core::mem::forget(arc);
        count
    }
    pub(crate) unsafe fn weak_count(ptr: TypeErasedPtr) -> usize {
        let arc = Self::as_arc(ptr);
        let count = Rc::weak_count(&arc);
        core::mem::forget(arc);
        count
    }
    pub(crate) unsafe fn clone_weak(ptr: TypeErasedPtr) {
        let weak = Self::as_weak(ptr);
        core::mem::forget(weak.clone());
        core::mem::forget(weak);
    }
    pub(crate) unsafe fn drop_weak(ptr: TypeErasedPtr) {
        let weak = Self::as_weak(ptr);
        core::mem::drop(weak);
    }
    pub(crate) unsafe fn upgrade_weak(ptr: TypeErasedPtr) -> Option<TypeErasedPtr> {
        let weak = Self::as_weak(ptr);
        let arc = weak.upgrade();
        core::mem::forget(weak);
        arc.map(|arc| TypeErasedPtr::new(Rc::into_raw(arc)))
    }
    pub(crate) unsafe fn strong_count_weak(ptr: TypeErasedPtr) -> usize {
        let weak = Self::as_weak(ptr);
        let count = Weak::strong_count(&weak);
        core::mem::forget(weak);
        count
    }
    pub(crate) unsafe fn weak_count_weak(ptr: TypeErasedPtr) -> usize {
        let weak = Self::as_weak(ptr);
        let count = Weak::weak_count(&weak);
        core::mem::forget(weak);
        count
    }

    pub(crate) unsafe fn as_arc(ptr: TypeErasedPtr) -> Rc<T> {
        Rc::from_raw(ptr.as_ptr())
    }

    pub(crate) unsafe fn as_weak(ptr: TypeErasedPtr) -> Weak<T> {
        Weak::from_raw(ptr.as_ptr())
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
