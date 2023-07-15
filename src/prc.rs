mod erased_rc;

use std::{hash::Hash, ops::Deref, ptr::NonNull, rc::Rc};

use erased_rc::{TypeErasedRc, TypeErasedWeak};

/// Parc because ProjectedArc
pub struct Prc<T: ?Sized> {
    rc: TypeErasedRc,
    projected: NonNull<T>,
}

impl<T> Prc<T> {
    pub fn new(value: T) -> Prc<T> {
        Rc::new(value).into()
    }
}

impl<T: ?Sized> Prc<T> {
    pub fn project_arc<'a, U: ?Sized>(arc: &'a Rc<U>, f: fn(&'a U) -> &'a T) -> Self {
        let projected = f(arc);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Self {
            rc: TypeErasedRc::new(arc.clone()),
            projected,
        }
    }

    pub fn project<'a, U: ?Sized>(&'a self, f: fn(&'a T) -> &'a U) -> Prc<U> {
        let projected = f(self);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const U as *mut U) };
        Prc::<U> {
            rc: self.rc.clone(),
            projected,
        }
    }

    pub fn downgrade(this: &Prc<T>) -> Weak<T> {
        Weak::<T> {
            weak: this.rc.downgrade(),
            projected: this.projected,
        }
    }

    pub fn weak_count(this: &Prc<T>) -> usize {
        this.rc.weak_count()
    }

    pub fn strong_count(this: &Prc<T>) -> usize {
        this.rc.strong_count()
    }

    pub fn ptr_eq(this: &Prc<T>, other: &Prc<T>) -> bool {
        std::ptr::eq(this.projected.as_ptr(), other.projected.as_ptr())
    }
}

impl<T: ?Sized> AsRef<T> for Prc<T> {
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> std::borrow::Borrow<T> for Prc<T> {
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> Clone for Prc<T> {
    fn clone(&self) -> Self {
        Self {
            rc: self.rc.clone(),
            projected: self.projected,
        }
    }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for Prc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parc")
            .field("projected", &self.deref())
            .finish()
    }
}

impl<T> std::fmt::Display for Prc<T>
where
    T: std::fmt::Display + ?Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: ?Sized> Deref for Prc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.projected.as_ref() }
    }
}

impl<T> std::error::Error for Prc<T>
where
    T: std::error::Error + ?Sized,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.deref().source()
    }
}

impl<T: ?Sized, F: Into<Rc<T>>> From<F> for Prc<T> {
    fn from(value: F) -> Self {
        Prc::project_arc(&value.into(), |x| x)
    }
}

impl<T> FromIterator<T> for Prc<[T]> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().collect::<Rc<[T]>>().into()
    }
}

impl<T> Hash for Prc<T>
where
    T: Hash + ?Sized,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<T> PartialEq<Prc<T>> for Prc<T>
where
    T: PartialEq<T> + ?Sized,
{
    fn eq(&self, other: &Prc<T>) -> bool {
        let this: &T = self;
        let other: &T = other;
        this.eq(other)
    }
}

impl<T> Eq for Prc<T> where T: Eq + ?Sized {}

impl<T> Ord for Prc<T>
where
    T: Ord + ?Sized,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let this: &T = self;
        let other: &T = other;
        this.cmp(other)
    }
}

impl<T> PartialOrd<Prc<T>> for Prc<T>
where
    T: PartialOrd<T> + ?Sized,
{
    fn partial_cmp(&self, other: &Prc<T>) -> Option<std::cmp::Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T> std::fmt::Pointer for Prc<T>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Pointer::fmt(&self.projected, f)
    }
}

impl<T> Unpin for Prc<T> where T: ?Sized {}
impl<T> std::panic::UnwindSafe for Prc<T> where T: std::panic::RefUnwindSafe + ?Sized {}

pub struct Weak<T: ?Sized> {
    weak: TypeErasedWeak,
    projected: NonNull<T>,
}

impl<T: ?Sized> Weak<T> {
    pub fn upgrade(&self) -> Option<Prc<T>> {
        Some(Prc {
            rc: self.weak.upgrade()?,
            projected: self.projected,
        })
    }

    pub fn strong_count(&self) -> usize {
        self.weak.strong_count()
    }

    pub fn weak_count(&self) -> usize {
        self.weak.weak_count()
    }
}

impl<T: ?Sized> Clone for Weak<T> {
    fn clone(&self) -> Self {
        Self {
            weak: self.weak.clone(),
            projected: self.projected,
        }
    }
}

impl<T: ?Sized> std::fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(Peak)")
    }
}
