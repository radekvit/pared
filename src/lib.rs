mod erased_arc;
mod erased_ptr;

use std::{hash::Hash, ops::Deref, sync::Arc};

use erased_arc::{TypeErasedArc, TypeErasedWeak};

trait Project<T: ?Sized> {
    fn project<'a, P: ?Sized>(&'a self, f: fn(&'a T) -> &'a P) -> Parc<P>;
}

impl<T: ?Sized> Project<T> for Arc<T> {
    #[inline]
    fn project<'a, P: ?Sized>(&'a self, f: fn(&'a T) -> &'a P) -> Parc<P> {
        Parc::project_arc(self, f)
    }
}
impl<T: ?Sized> Project<T> for Parc<T> {
    #[inline]
    fn project<'a, P: ?Sized>(&'a self, f: fn(&'a T) -> &'a P) -> Parc<P> {
        Parc::project(self, f)
    }
}
/// Parc because ProjectedArc
#[derive(Clone)]
pub struct Parc<P: ?Sized> {
    arc: TypeErasedArc,
    projected: *const P,
}

impl<T: ?Sized> Parc<T> {
    pub fn project_arc<'a, U: ?Sized>(arc: &'a Arc<U>, f: fn(&'a U) -> &'a T) -> Self {
        let projected = f(arc);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = projected as *const T;
        Self {
            arc: TypeErasedArc::new(arc.clone()),
            projected,
        }
    }

    pub fn project<'a, U: ?Sized>(&'a self, f: fn(&'a T) -> &'a U) -> Parc<U> {
        let projected = f(self);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = projected as *const U;
        Parc::<U> {
            arc: self.arc.clone(),
            projected,
        }
    }

    pub fn downgrade(this: &Parc<T>) -> Peak<T> {
        Peak::<T> {
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
        std::ptr::eq(this.projected, other.projected)
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
        unsafe { &*self.projected }
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

impl<T: ?Sized> From<Arc<T>> for Parc<T> {
    fn from(value: Arc<T>) -> Self {
        Parc::project_arc(&value, |x| x)
    }
}

impl<T: ?Sized> From<Box<T>> for Parc<T> {
    fn from(value: Box<T>) -> Self {
        Arc::<T>::from(value).into()
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
        self.deref() == other.deref()
    }
}

impl<T> Eq for Parc<T> where T: Eq + ?Sized {}

impl<T> Ord for Parc<T>
where
    T: Ord + ?Sized,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.deref().cmp(other)
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

#[derive(Clone)]
pub struct Peak<T: ?Sized> {
    weak: TypeErasedWeak,
    projected: *const T,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Peak<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Peak<T> {}

impl<T: ?Sized> Peak<T> {
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

impl<T: ?Sized> std::fmt::Debug for Peak<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(Peak)")
    }
}
