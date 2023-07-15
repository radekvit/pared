mod erased_arc;

use std::{hash::Hash, ops::Deref, ptr::NonNull, sync::Arc};

use erased_arc::{TypeErasedArc, TypeErasedWeak};

/// Parc because ProjectedArc
pub struct Parc<T: ?Sized> {
    arc: TypeErasedArc,
    projected: NonNull<T>,
}

impl<T> Parc<T>
where
    T: Send + Sync,
{
    pub fn new(value: T) -> Parc<T> {
        Arc::new(value).into()
    }
}

impl<T: ?Sized> Parc<T> {
    pub fn project_arc<'a, U: ?Sized>(arc: &'a Arc<U>, f: fn(&'a U) -> &'a T) -> Self
    where
        U: Send + Sync,
    {
        let projected = f(arc);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Self {
            arc: TypeErasedArc::new(arc.clone()),
            projected,
        }
    }

    pub fn project<'a, U: ?Sized>(&'a self, f: fn(&'a T) -> &'a U) -> Parc<U> {
        let projected = f(self);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const U as *mut U) };
        Parc::<U> {
            arc: self.arc.clone(),
            projected,
        }
    }

    pub fn downgrade(this: &Parc<T>) -> Weak<T> {
        Weak::<T> {
            weak: this.arc.downgrade(),
            projected: this.projected,
        }
    }

    pub fn weak_count(this: &Parc<T>) -> usize {
        this.arc.weak_count()
    }

    pub fn strong_count(this: &Parc<T>) -> usize {
        this.arc.strong_count()
    }

    pub fn ptr_eq(this: &Parc<T>, other: &Parc<T>) -> bool {
        std::ptr::eq(this.projected.as_ptr(), other.projected.as_ptr())
    }
}

impl<T: ?Sized> AsRef<T> for Parc<T> {
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> std::borrow::Borrow<T> for Parc<T> {
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> Clone for Parc<T> {
    fn clone(&self) -> Self {
        Self {
            arc: self.arc.clone(),
            projected: self.projected,
        }
    }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for Parc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parc")
            .field("projected", &self.deref())
            .finish()
    }
}

impl<T> std::fmt::Display for Parc<T>
where
    T: std::fmt::Display + ?Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: ?Sized> Deref for Parc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.projected.as_ref() }
    }
}

impl<T> std::error::Error for Parc<T>
where
    T: std::error::Error + ?Sized,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.deref().source()
    }
}

impl<T, F> From<F> for Parc<T>
where
    T: ?Sized + Send + Sync,
    F: Into<Arc<T>>,
{
    fn from(value: F) -> Self {
        Parc::project_arc(&value.into(), |x| x)
    }
}

impl<T> FromIterator<T> for Parc<[T]>
where
    T: Send + Sync,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().collect::<Arc<[T]>>().into()
    }
}

impl<T> Hash for Parc<T>
where
    T: Hash + ?Sized,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<T> PartialEq<Parc<T>> for Parc<T>
where
    T: PartialEq<T> + ?Sized,
{
    fn eq(&self, other: &Parc<T>) -> bool {
        let this: &T = self;
        let other: &T = other;
        this.eq(other)
    }
}

impl<T> Eq for Parc<T> where T: Eq + ?Sized {}

impl<T> Ord for Parc<T>
where
    T: Ord + ?Sized,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let this: &T = self;
        let other: &T = other;
        this.cmp(other)
    }
}

impl<T> PartialOrd<Parc<T>> for Parc<T>
where
    T: PartialOrd<T> + ?Sized,
{
    fn partial_cmp(&self, other: &Parc<T>) -> Option<std::cmp::Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T> std::fmt::Pointer for Parc<T>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Pointer::fmt(&self.projected, f)
    }
}

unsafe impl<T> Send for Parc<T> where T: Sync + Send + ?Sized {}
unsafe impl<T> Sync for Parc<T> where T: Sync + Send + ?Sized {}

impl<T> Unpin for Parc<T> where T: ?Sized {}
impl<T> std::panic::UnwindSafe for Parc<T> where T: std::panic::RefUnwindSafe + ?Sized {}

pub struct Weak<T: ?Sized> {
    weak: TypeErasedWeak,
    projected: NonNull<T>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Weak<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Weak<T> {}

impl<T: ?Sized> Weak<T> {
    pub fn upgrade(&self) -> Option<Parc<T>> {
        Some(Parc {
            arc: self.weak.upgrade()?,
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
