//! Projected atomic reference-counted pointers.
//!
//! Available pointer types:
//! - [`Parc`]
//! - [`Weak`]
//!
//! # Example
//! ```
//! # use std::sync::Arc;
//! # use parc::sync::{Parc, Weak};
//! fn accepts_parc(parc: Parc<u8>) {}
//!
//! // Parc can be created by projecting references from an Arc
//! let from_tuple = Parc::from_arc(&Arc::new((16usize, 8u8)), |tuple| &tuple.1);
//! // Or by using any T: Into<Arc<_>>
//! let from_u8: Parc<u8> = Parc::new(8u8);
//!
//! std::thread::spawn(move || {
//!     // Functions accept any Parc<T>, regardless of which Arc<U> it was created from
//!     if (true) {
//!         accepts_parc(from_tuple);
//!     } else {
//!         accepts_parc(from_u8);
//!     }
//! });
//! ```
//!
//! Parc can only be created from `Arc`s (or other `Parc`s) for `T: Send + Sync`.
//!
//! ```compile_fail
//! # use std::sync::Arc;
//! # use parc::sync::Parc;
//! // Error: Parc can only be backed by a Sync
//! let parc = Arc::new(&1 as *const _).into();
//! ```
//! ```compile_fail
//! # use std::sync::Arc;
//! # use parc::sync::Parc;
//! let parc = Parc::new(1);
//! // This Parc is !Send and !Sync
//! let no_send = parc.project(|x| &(&1u8 as *const u8));
//! // Error
//! let denied = no_send.project(|x| x);
//! ```

mod erased_arc;

use alloc::sync::Arc;
use core::{
    clone::Clone,
    cmp::{Eq, Ord, PartialEq, PartialOrd},
    convert::{AsRef, From, Into},
    hash::Hash,
    iter::{FromIterator, IntoIterator},
    marker::{Send, Sized, Sync, Unpin},
    ops::Deref,
    ops::FnOnce,
    option::{Option, Option::Some},
    ptr::NonNull,
};

use erased_arc::{TypeErasedArc, TypeErasedWeak};

/// Projected atomic reference counted pointer.
///
/// This is a projected version of [`core::sync::Arc`] that points to any (sub)member of the original
/// `Arc`'s data. Instances created from different types of `Arc<T>`s are interchangable.
///
/// This type implements most of `Arc`'s API surface, with the exception of operations that require
/// access to the original `Arc`'s type, which is unavailable from this type.
///
/// # Example
/// ```
/// # use std::sync::Arc;
/// # use parc::sync::{Parc, Weak};
/// fn accepts_parc(parc: Parc<u8>) {}
///
/// // Parc can be created by projecting references from an Arc
/// let from_tuple = Parc::from_arc(&Arc::new((16usize, 8u8)), |tuple| &tuple.1);
/// // Or by using any T: Into<Arc<_>>
/// let from_u8: Parc<u8> = Parc::new(8u8);
///
/// std::thread::spawn(move || {
///     // Functions accept any Parc<T>, regardless of which Arc<U> it was created from
///     if (true) {
///         accepts_parc(from_tuple);
///     } else {
///         accepts_parc(from_u8);
///     }
/// });
/// ```
///
/// Parc can only be created from `Arc`s (or other `Parc`s) for `T: Send + Sync`.
///
/// ```compile_fail
/// # use std::sync::Arc;
/// # use parc::sync::Parc;
/// // Error: Parc can only be backed by a Sync
/// let parc = Arc::new(&1 as *const _).into();
/// ```
/// ```compile_fail
/// # use std::sync::Arc;
/// # use parc::sync::Parc;
/// let parc = Parc::new(1);
/// // This Parc is !Send and !Sync
/// let no_send = parc.project(|x| &(&1u8 as *const u8));
/// // Error
/// let denied = no_send.project(|x| x);
/// ```
pub struct Parc<T: ?Sized> {
    arc: TypeErasedArc,
    projected: NonNull<T>,
}

impl<T> Parc<T>
where
    T: Send + Sync,
{
    /// Constructs a new `Parc<T>`.
    ///
    /// # Example
    /// ```
    /// use parc::sync::Parc;
    /// let parc = Parc::new(6);
    /// ```
    pub fn new(value: T) -> Parc<T> {
        Arc::new(value).into()
    }
}

impl<T: ?Sized> Parc<T> {
    /// Constructs a new `Parc<T>` from an existing `Arc<T>`.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the arc won't be cloned.
    ///
    /// # Example
    pub fn from_arc<U, F>(arc: &Arc<U>, project: F) -> Self
    where
        U: ?Sized + Send + Sync,
        F: for<'x> FnOnce(&'x U) -> &'x T,
    {
        let projected = project(arc);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Self {
            arc: TypeErasedArc::new(arc.clone()),
            projected,
        }
    }

    pub fn project<U: ?Sized, F: for<'x> FnOnce(&'x T) -> &'x U>(&self, project: F) -> Parc<U>
    where
        T: Send + Sync,
    {
        let projected = project(self);
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
        core::ptr::eq(this.projected.as_ptr(), other.projected.as_ptr())
    }
}

impl<T: ?Sized> AsRef<T> for Parc<T> {
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> core::borrow::Borrow<T> for Parc<T> {
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

impl<T: ?Sized + core::fmt::Debug> core::fmt::Debug for Parc<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Parc")
            .field("projected", &self.deref())
            .finish()
    }
}

impl<T> core::fmt::Display for Parc<T>
where
    T: core::fmt::Display + ?Sized,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

#[cfg(feature = "std")]
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
        Parc::from_arc(&value.into(), |x| x)
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
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
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
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let this: &T = self;
        let other: &T = other;
        this.cmp(other)
    }
}

impl<T> PartialOrd<Parc<T>> for Parc<T>
where
    T: PartialOrd<T> + ?Sized,
{
    fn partial_cmp(&self, other: &Parc<T>) -> Option<core::cmp::Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T> core::fmt::Pointer for Parc<T>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Pointer::fmt(&self.projected, f)
    }
}

unsafe impl<T> Send for Parc<T> where T: Sync + Send + ?Sized {}
unsafe impl<T> Sync for Parc<T> where T: Sync + Send + ?Sized {}

impl<T> Unpin for Parc<T> where T: ?Sized {}
impl<T> core::panic::UnwindSafe for Parc<T> where T: core::panic::RefUnwindSafe + ?Sized {}

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

impl<T: ?Sized> core::fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(Peak)")
    }
}
