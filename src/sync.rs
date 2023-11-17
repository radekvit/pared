//! Projected atomic reference-counted pointers.
//!
//! Available pointer types:
//! - [`Parc`]
//! - [`Weak`]
//!
//! # Example
//! ```
//! # use std::sync::Arc;
//! use pared::sync::{Parc, Weak};
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
//! ```compile_fail,E0277
//! # use std::sync::Arc;
//! use pared::sync::Parc;
//! // This Arc is !Send + !Sync
//! let arc: Arc<*const i32> = Arc::new(&1 as *const i32);
//! // Error: Parc can only be backed by an Arc<T>: Send + Sync
//! let parc: Parc<*const i32> = arc.into();
//! ```
//! ```compile_fail,E0277
//! # use std::sync::Arc;
//! use pared::sync::Parc;
//! let parc = Parc::new(1);
//! // This Parc is !Send and !Sync
//! let no_send = parc.project(|x| &(&1u8 as *const u8));
//! // Error
//! let denied = no_send.project(|x| x);
//! ```
//!
//! # Soundness
//! None of the following should compile:
//!
//! ```compile_fail,E0597
//! use pared::sync::Parc;
//! use std::sync::Arc;
//!
//! let x: Arc<()> = Arc::new(());
//! let z: Parc<str>;
//! {
//!     let s = "Hello World!".to_string();
//!     let s_ref: &str = &s;
//!     let y: Parc<&str> = Parc::from_arc(&x, |_| &s_ref);
//!     z = y.project(|s: &&str| *s);
//!     // s deallocated here
//! }
//! println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
//! ```
//!
//! ```compile_fail,E0597
//! use pared::sync::Parc;
//!
//! let x: Parc<()> = Parc::new(());
//! let z: Parc<str>;
//! {
//!     let s = "Hello World!".to_string();
//!     let s_ref: &str = &s;
//!     let y: Parc<&str> = x.project(|_| &s_ref);
//!     z = y.project(|s: &&str| *s);
//!     // s deallocated here
//! }
//! println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
//! ```
//!
//! ```compile_fail,E0597
//! use pared::sync::Parc;
//!
//! let x: Parc<()> = Parc::new(());
//! let z: Parc<str>;
//! {
//!     let s = "Hello World!".to_string();
//!     z = x.project(|_| &s as &str);
//!     // s deallocated here
//! }
//! println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
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
/// This is a projected version of [`Arc`] that points to any (sub)member of the original.
/// `Arc`'s data. Instances created from different types of `Arc<T>`s are interchangable.
///
/// This type implements most of `Arc`'s API surface, with the exception of operations that require
/// access to the original `Arc`'s type, which is unavailable from this type.
///
/// # Example
/// ```
/// # use std::sync::Arc;
/// use pared::sync::{Parc, Weak};
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
/// ```compile_fail,E0277
/// # use std::sync::Arc;
/// use pared::sync::Parc;
/// // Create an Arc that's !Send + !Sync
/// let arc: Arc<*const i32> = Arc::new(&1 as *const i32);
/// // Error: Parc can only be backed by an Arc<T>: Send + Sync
/// let parc: Parc<*const i32> = arc.into();
/// ```
/// ```compile_fail,E0277
/// # use std::sync::Arc;
/// use pared::sync::Parc;
/// let parc = Parc::new(1);
/// // This Parc is !Send and !Sync
/// let no_send = parc.project(|_| &(&1u8 as *const u8));
/// // Error
/// let denied = no_send.project(|x| x);
/// ```
///
/// [`Arc`]: https://doc.rust-lang.org/std/sync/struct.Arc.html
pub struct Parc<T: ?Sized> {
    arc: TypeErasedArc,
    projected: NonNull<T>,
}

impl<T> Parc<T>
where
    T: Send + Sync + 'static,
{
    /// Constructs a new `Parc<T>`.
    ///
    /// # Example
    /// ```
    /// use pared::sync::Parc;
    /// let parc = Parc::new(6);
    /// ```
    #[inline]
    pub fn new(value: T) -> Parc<T> {
        Arc::new(value).into()
    }
}

impl<T: ?Sized> Parc<T> {
    /// Constructs a new `Parc<T>` from an existing `Arc<T>` by projecting a field.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the arc won't be cloned.
    ///
    /// # Example
    /// ```
    /// # use std::sync::Arc;
    /// use pared::sync::Parc;
    /// let arc = Arc::new((5u64,));
    /// let parc = Parc::from_arc(&arc, |tuple| &tuple.0);
    /// ```
    ///
    /// Note that references to local variables cannot be returned from the `project` function:
    /// ```compile_fail,E0597
    /// # use std::sync::Arc;
    /// use pared::sync::Parc;
    /// let arc = Arc::new((5u64,));
    /// let local = 5;
    /// let parc = Parc::from_arc(&arc, |tuple| &local);
    /// ```
    #[inline]
    pub fn from_arc<U, F>(arc: &Arc<U>, project: F) -> Self
    where
        T: 'static,
        U: ?Sized + Send + Sync,
        F: FnOnce(&U) -> &T,
    {
        let projected = project(arc);
        // SAFETY: the returned reference always converts to a non-null pointer.
        // It's safe to convert the returned reference to a pointer (and then convert it in `Deref`)
        // because the lifetime of the reference returned by `F` must be either the lifetime
        // of the local reference passed to it, or 'static
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Self {
            arc: TypeErasedArc::new(arc.clone()),
            projected,
        }
    }

    /// Constructs a new `Option<Parc<T>>` from an existing `Arc<T>` by trying to project a field.
    ///
    /// If the function passed into this returns `None`, this method will also return `None`.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the rc won't be cloned.
    ///
    /// # Example
    /// ```
    /// use std::sync::Arc;
    /// use pared::sync::Parc;
    ///
    /// enum Enum {
    ///     Str(String),
    ///     Int(isize),
    /// }
    ///
    /// let arc = Arc::new(Enum::Int(5));
    /// let parc = Parc::try_from_arc(&arc, |x| match x {
    ///     Enum::Str(s) => None,
    ///     Enum::Int(i) => Some(i),
    /// });
    ///
    /// assert!(matches!(parc, Some(parc) if *parc == 5 ));
    /// ```
    #[inline]
    pub fn try_from_arc<U, F>(arc: &Arc<U>, project: F) -> Option<Self>
    where
        U: ?Sized + Sync + Send,
        T: 'static,
        F: FnOnce(&U) -> Option<&T>,
    {
        let projected = project(arc)?;
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Some(Self {
            arc: TypeErasedArc::new(arc.clone()),
            projected,
        })
    }

    /// Constructs a new `Parc<T>` from an existing `Parc<T>` by projecting a field.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the underlying arc won't be cloned.
    ///
    /// # Example
    /// ```
    /// use pared::sync::Parc;
    /// let parc = Parc::new((5u64,));
    /// let projected = parc.project(|tuple| &tuple.0);
    /// ```
    ///
    /// Note that references to local variables cannot be returned from the `project` function:
    /// ```compile_fail,E0597
    /// use pared::sync::Parc;
    /// let parc = Parc::new((5u64,));
    /// let local = 5;
    /// let projected = parc.project(|tuple| &local);
    /// ```
    #[inline]
    pub fn project<U, F>(&self, project: F) -> Parc<U>
    where
        T: Send + Sync,
        U: ?Sized + 'static,
        F: FnOnce(&T) -> &U,
    {
        let projected = project(self);
        // SAFETY: the returned reference always converts to a non-null pointer.
        // It's safe to convert the returned reference to a pointer (and then convert it in `Deref`)
        // because the lifetime of the reference returned by `F` must be either the lifetime
        // of the local reference passed to it, or 'static
        let projected = unsafe { NonNull::new_unchecked(projected as *const U as *mut U) };
        Parc::<U> {
            arc: self.arc.clone(),
            projected,
        }
    }

    /// Constructs a new `Option<Parc<T>>` from an existing `Parc<T>`
    /// by trying to projecting a field.
    ///
    /// If the function passed into this returns `None`, this method will also return `None`.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the underlying rc won't be cloned.
    ///
    /// # Example
    /// ```
    /// use pared::sync::Parc;
    ///
    /// enum Enum {
    ///     Str(String),
    ///     Int(isize),
    /// }
    ///
    /// let prc = Parc::new(Enum::Int(5));
    /// let projected = prc.try_project(|x| match x {
    ///     Enum::Str(s) => None,
    ///     Enum::Int(i) => Some(i),
    /// });
    ///
    /// assert!(matches!(projected, Some(p) if *p == 5 ));
    /// ```
    pub fn try_project<U, F>(&self, project: F) -> Option<Parc<U>>
    where
        T: Send + Sync,
        U: ?Sized + 'static,
        F: for<'x> FnOnce(&'x T) -> Option<&'x U>,
    {
        let projected = project(self)?;
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const U as *mut U) };
        Some(Parc::<U> {
            arc: self.arc.clone(),
            projected,
        })
    }
    /// Provides a raw pointer to the data.
    ///
    /// The counts are not affected in any way and the `Parc` is not consumed. The pointer is valid for
    /// as long as there are strong counts in the `Parc` or in the underlying `Arc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pared::sync::Parc;
    ///
    /// let x = Parc::new("hello".to_owned());
    /// let y = Parc::clone(&x);
    /// let x_ptr = Parc::as_ptr(&x);
    /// assert_eq!(x_ptr, Parc::as_ptr(&y));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    #[must_use]
    pub fn as_ptr(this: &Self) -> *const T {
        NonNull::as_ptr(this.projected)
    }

    /// Creates a new `Weak` pointer to this allocation.
    ///
    /// This `Weak` pointer is tied to strong references to the original `Arc`, meaning it's not
    /// tied to instances of the `Parc` it was created from.
    ///
    /// # Example
    /// ```
    /// # use std::sync::Arc;
    /// use pared::sync::Parc;
    /// let arc = Arc::new((42,));
    /// let weak = {
    ///     let parc = Parc::from_arc(&arc, |tuple| &tuple.0);
    ///     Parc::downgrade(&parc)
    /// };
    /// let stored = weak.upgrade().map(|parc| *parc);
    /// assert_eq!(stored, Some(42));
    /// ```
    #[inline]
    pub fn downgrade(this: &Parc<T>) -> Weak<T> {
        Weak::<T> {
            weak: this.arc.downgrade(),
            projected: this.projected,
        }
    }

    /// Gets the number of [`Weak`] pointers to this allocation.
    ///
    /// See [`Arc::weak_count`].
    ///
    /// # Safety
    /// This method by itself is safe, but using it correctly requires extra care.
    /// Another thread can change the weak count at any time, including potentially between
    /// calling this method and acting on the result.
    ///
    /// # Example
    /// ```
    /// use pared::sync::Parc;
    /// let six = Parc::new(6);
    /// let _weak_six = Parc::downgrade(&six);
    ///
    /// // Deterministic because we didn't share between threads
    /// assert_eq!(Parc::weak_count(&six), 1);
    /// ```
    ///
    /// [`Arc::weak_count`]: https://doc.rust-lang.org/std/sync/struct.Arc.html#method.weak_count
    #[inline]
    pub fn weak_count(this: &Parc<T>) -> usize {
        this.arc.weak_count()
    }

    /// Gets the number of strong pointers to this allocation.
    ///
    /// See [`Arc::strong_count`].
    ///
    /// # Safety
    /// This method by itself is safe, but using it correctly requires extra care.
    /// Another thread can change the weak count at any time, including potentially between
    /// calling this method and acting on the result.
    ///
    /// # Example
    /// ```
    /// use pared::sync::Parc;
    /// let six = Parc::new(6);
    /// let _also_six = six.clone();
    ///
    /// // Deterministic because we didn't share between threads
    /// assert_eq!(Parc::strong_count(&six), 2);
    /// ```
    ///
    /// [`Arc::weak_count`]: https://doc.rust-lang.org/std/sync/struct.Arc.html#method.strong_count
    #[inline]
    pub fn strong_count(this: &Parc<T>) -> usize {
        this.arc.strong_count()
    }

    /// Returns `true` if the two `Parc`s point to the same data, using [`core::ptr::eq`].
    /// See that function for caveats when comparing `dyn Trait` pointers.
    ///
    /// # Example
    /// ```
    /// use pared::sync::Parc;
    ///
    /// let five = Parc::new(5);
    /// let same_five = five.clone();
    /// let other_five = Parc::new(5);
    ///
    /// assert!(Parc::ptr_eq(&five, &same_five));
    /// assert!(!Parc::ptr_eq(&five, &other_five));
    /// ```
    ///
    /// [`core::ptr::eq`]: https://doc.rust-lang.org/core/ptr/fn.eq.html
    pub fn ptr_eq(this: &Parc<T>, other: &Parc<T>) -> bool {
        core::ptr::eq(this.projected.as_ptr(), other.projected.as_ptr())
    }
}

impl<T: ?Sized> AsRef<T> for Parc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> core::borrow::Borrow<T> for Parc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> Clone for Parc<T> {
    #[inline]
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
        // SAFETY: projected is safely constructed only in `from_arc` or `project`,
        // where we guarantee the pointer will be valid as long as the original `Arc` lives.
        unsafe { self.projected.as_ref() }
    }
}

#[cfg(feature = "std")]
impl<T> std::error::Error for Parc<T>
where
    T: std::error::Error + ?Sized,
{
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.deref().source()
    }
}

impl<T, F> From<F> for Parc<T>
where
    T: ?Sized + Send + Sync + 'static,
    F: Into<Arc<T>>,
{
    #[inline]
    fn from(value: F) -> Self {
        Parc::from_arc(&value.into(), |x| x)
    }
}

impl<T> FromIterator<T> for Parc<[T]>
where
    T: Send + Sync + 'static,
{
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().collect::<Arc<[T]>>().into()
    }
}

impl<T> Hash for Parc<T>
where
    T: Hash + ?Sized,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<T> PartialEq<Parc<T>> for Parc<T>
where
    T: PartialEq<T> + ?Sized,
{
    #[inline]
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
    #[inline]
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
    #[inline]
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

// SAFETY: We can only create Parc from either
// Arc<T> where T: Send + Sync
// or
// Parc<T> where T: Send + Sync
// which guarantees that as long as our projected T is also Send + Sync,
// we can safely send Parc<T> between threads
unsafe impl<T> Send for Parc<T> where T: Sync + Send + ?Sized {}
// SAFETY: We can only create Parc from either
// Arc<T> where T: Send + Sync
// or
// Parc<T> where T: Send + Sync
// which guarantees that as long as our projected T is also Send + Sync,
// we can safely send &Parc<T> between threads
unsafe impl<T> Sync for Parc<T> where T: Sync + Send + ?Sized {}

impl<T> Unpin for Parc<T> where T: ?Sized {}
impl<T> core::panic::UnwindSafe for Parc<T> where T: core::panic::RefUnwindSafe + ?Sized {}

/// Weak is a version of [`Parc`] that holds a non-owning reference to the managed allocation.
/// The allocation is accessed by calling [`upgrade`], which returns `Option<Parc<T>>`.
///
/// `Weak` will be valid as long as the original allocation is alive; it's not tied to the specific
/// `Parc` it was created from.
///
/// See [`std::sync::Weak`] for more details.
///
/// # Example
/// ```
/// use pared::sync::{Parc, Weak};
///
/// let tuple = Parc::new((7, 8));
/// let weak: Weak<(usize, usize)> = Parc::downgrade(&tuple);
/// let projected = tuple.project(|x| &x.1);
/// drop(tuple);
///
/// // Even when tuple is dropped, we can still access it using Weak
/// let tuple = weak.upgrade().unwrap();
/// assert_eq!(*tuple, (7, 8));
///
/// // When we drop all strong references, Weak::upgrade will return None
/// drop(tuple);
/// drop(projected);
/// assert_eq!(weak.upgrade(), None);
/// ```
///
/// [`upgrade`]: Weak::upgrade
/// [`std::sync::Weak`]: https://doc.rust-lang.org/std/sync/struct.Weak.html
pub struct Weak<T: ?Sized> {
    weak: TypeErasedWeak,
    projected: NonNull<T>,
}

// SAFETY: We can only create Parc from either
// Arc<T> where T: Send + Sync
// or
// Parc<T> where T: Send + Sync
// and Weak<T> is only ever constructed from Parc<T>,
// which guarantees that as long as our projected T is also Send + Sync,
// we can safely send Weak<T> between threads.

unsafe impl<T: ?Sized + Sync + Send> Send for Weak<T> {}
// SAFETY: We can only create Parc from either
// Arc<T> where T: Send + Sync
// or
// Parc<T> where T: Send + Sync
// and Weak<T> is only ever constructed from Parc<T>,
// which guarantees that as long as our projected T is also Send + Sync,
// we can safely send Weak<T> between threads.
unsafe impl<T: ?Sized + Sync + Send> Sync for Weak<T> {}

impl<T: ?Sized> Weak<T> {
    /// Returns a raw pointer to the object `T` pointed to by this `Weak<T>`.
    ///
    /// The pointer is valid only if there are some strong references.
    ///
    /// # Examples
    ///
    /// ```
    /// use pared::sync::Parc;
    /// use std::ptr;
    ///
    /// let strong = Parc::new("hello".to_owned());
    /// let weak = Parc::downgrade(&strong);
    /// // Both point to the same object
    /// assert!(ptr::eq(&*strong, weak.as_ptr()));
    /// // The strong here keeps it alive, so we can still access the object.
    /// assert_eq!("hello", unsafe { &*weak.as_ptr() });
    ///
    /// drop(strong);
    /// // But not any more. We can do weak.as_ptr(), but accessing the pointer would lead to
    /// // undefined behaviour.
    /// // assert_eq!("hello", unsafe { &*weak.as_ptr() });
    /// ```
    ///
    /// [`null`]: core::ptr::null "ptr::null"
    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        NonNull::as_ptr(self.projected)
    }

    /// Attempts to upgrade the `Weak` pointer to a [`Parc`], delaying dropping of the inner value
    /// if successful.
    ///
    /// Returns [`None`] if the inner value has since been dropped.
    ///
    /// # Example
    /// ```
    ///
    /// use pared::sync::Parc;
    /// let five = Parc::new(5);
    ///
    /// let weak_five = Parc::downgrade(&five);
    ///
    /// let strong_five: Option<Parc<_>> = weak_five.upgrade();
    /// assert!(strong_five.is_some());
    ///
    /// // Destroy all strong pointers.
    /// drop(strong_five);
    /// drop(five);
    ///
    /// assert!(weak_five.upgrade().is_none());
    /// ```
    #[inline]
    pub fn upgrade(&self) -> Option<Parc<T>> {
        Some(Parc {
            arc: self.weak.upgrade()?,
            projected: self.projected,
        })
    }

    /// Returns the number of strong pointers pointing to this allocation.
    #[inline]
    pub fn strong_count(&self) -> usize {
        self.weak.strong_count()
    }

    /// Gets an approximation of the number of `Weak` pointers pointing to this allocation.
    ///
    /// See [`std::sync::Weak::weak_count`] for more details.
    ///
    /// [`std::sync::Weak::weak_count`]: https://doc.rust-lang.org/std/sync/struct.Weak.html#method.weak_count
    #[inline]
    pub fn weak_count(&self) -> usize {
        self.weak.weak_count()
    }

    /// Returns `true` if the two `Weak`s point to the same data, using [`core::ptr::eq`].
    /// See that function for caveats when comparing `dyn Trait` pointers.
    ///
    /// This function is able to compare `Weak` pointers even when either or both of them
    /// can't successfully `upgrade` anymore.
    #[inline]
    pub fn ptr_eq(&self, other: &Weak<T>) -> bool {
        core::ptr::eq(self.projected.as_ptr(), other.projected.as_ptr())
    }
}

impl<T: ?Sized> Clone for Weak<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            weak: self.weak.clone(),
            projected: self.projected,
        }
    }
}

impl<T: ?Sized> core::fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(Weak)")
    }
}
