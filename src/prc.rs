//! Projected reference-counted pointers.
//!
//! Available pointer types:
//! - [`Prc`]
//! - [`Weak`]
//!
//! # Example
//! ```
//! # use std::rc::Rc;
//! use pared::prc::{Prc, Weak};
//! fn accepts_prc(prc: Prc<u8>) {}
//!
//! // Prc can be created by projecting references from an Rc
//! let from_tuple = Prc::from_rc(&Rc::new((16usize, 8u8)), |tuple| &tuple.1);
//! // Or by using any T: Into<Rc<_>>
//! let from_u8: Prc<u8> = Prc::new(8u8);
//!
//! // Functions accept any Prc<T>, regardless of which Rc<U> it was created from
//! if (true) {
//!     accepts_prc(from_tuple);
//! } else {
//!     accepts_prc(from_u8);
//! }
//! ```
//! //! # Soundness
//! None of the following should compile:
//!
//! ```compile_fail
//! use pared::prc::Prc;
//! use std::rc::Rc;
//!
//! let x: Rc<()> = Rc::new(());
//! let z: Prc<str>;
//! {
//!     let s = "Hello World!".to_string();
//!     let s_ref: &str = &s;
//!     let y: Prc<&str> = Prc::from_rc(|_| &s_ref);
//!     z = y.project(|s: &&str| *s);
//!     // s deallocated here
//! }
//! println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
//! ```
//!
//! ```compile_fail
//! use pared::prc::Prc;
//!
//! let x: Prc<()> = Prc::new(());
//! let z: Prc<str>;
//! {
//!     let s = "Hello World!".to_string();
//!     let s_ref: &str = &s;
//!     let y: Prc<&str> = x.project(|_| &s_ref);
//!     z = y.project(|s: &&str| *s);
//!     // s deallocated here
//! }
//! println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
//! ```
//!
//! ```compile_fail
//! use pared::prc::Prc;
//! use std::sync::Arc;
//!
//! let x: Prc<()> = Prc::new(());
//! let z: Prc<str>;
//! {
//!     let s = "Hello World!".to_string();
//!     z = x.project(|_| &s as &str);
//!     // s deallocated here
//! }
//! println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
//! ```

mod erased_rc;

use alloc::rc::Rc;
use core::{
    clone::Clone,
    cmp::{Eq, Ord, PartialEq, PartialOrd},
    convert::{AsRef, From, Into},
    hash::Hash,
    iter::{FromIterator, IntoIterator},
    marker::{Sized, Unpin},
    ops::Deref,
    ops::FnOnce,
    option::{Option, Option::Some},
    ptr::NonNull,
};

use erased_rc::{TypeErasedRc, TypeErasedWeak};

/// Projected reference counted pointer.
///
/// This is a projected version of [`Rc`] that points to any (sub)member of the original
/// `Rc`'s data. Instances created from different types of `Rc<T>`s are interchangable.
///
/// This type implements most of `Rc`'s API surface, with the exception of operations that require
/// access to the original `Rc`'s type, which is unavailable from this type.
///
/// # Example
/// ```
/// # use std::rc::Rc;
/// use pared::prc::{Prc, Weak};
/// fn accepts_prc(prc: Prc<u8>) {}
///
/// // Prc can be created by projecting references from an Rc
/// let from_tuple = Prc::from_rc(&Rc::new((16usize, 8u8)), |tuple| &tuple.1);
/// // Or by using any T: Into<Rc<_>>
/// let from_u8: Prc<u8> = Prc::new(8u8);
///
/// // Functions accept any Prc<T>, regardless of which Rc<U> it was created from
/// if (true) {
///     accepts_prc(from_tuple);
/// } else {
///     accepts_prc(from_u8);
/// }
/// ```
///
/// [`Rc`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
pub struct Prc<T: ?Sized> {
    rc: TypeErasedRc,
    projected: NonNull<T>,
}

impl<T> Prc<T>
where
    T: 'static,
{
    /// Constructs a new `Prc<T>`.
    ///
    /// # Example
    /// ```
    /// use pared::prc::Prc;
    /// let prc = Prc::new(6);
    /// ```
    pub fn new(value: T) -> Prc<T> {
        Rc::new(value).into()
    }
}

impl<T: ?Sized> Prc<T> {
    /// Constructs a new `Prc<T>` from an existing `Rc<T>` by projecting a field.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the rc won't be cloned.
    ///
    /// # Example
    /// ```
    /// # use std::rc::Rc;
    /// use pared::prc::Prc;
    /// let rc = Rc::new((5u64,));
    /// let prc = Prc::from_rc(&rc, |tuple| &tuple.0);
    /// ```
    ///
    /// Note that references to local variables cannot be returned from the `project` function:
    /// ```compile_fail
    /// # use std::rc::Rc;
    /// use pared::prc::Prc;
    /// let rc = Rc::new((5u64,));
    /// let local = 5;
    /// let prc = Prc::from_rc(&rc, |tuple| &local);
    /// ```
    #[inline]
    pub fn from_rc<U, F>(rc: &Rc<U>, project: F) -> Self
    where
        U: ?Sized,
        T: 'static,
        F: for<'x> FnOnce(&'x U) -> &'x T,
    {
        let projected = project(rc);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Self {
            rc: TypeErasedRc::new(rc.clone()),
            projected,
        }
    }

    /// Constructs a new `Option<Prc<T>>` from an existing `Rc<T>` by trying to project a field.
    ///
    /// If the function passed into this returns `None`, this method will also return `None`.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the rc won't be cloned.
    ///
    /// # Example
    /// ```
    /// use std::rc::Rc;
    /// use pared::prc::Prc;
    ///
    /// enum Enum {
    ///     Str(String),
    ///     Int(isize),
    /// }
    ///
    /// let rc = Rc::new(Enum::Int(5));
    /// let prc = Prc::try_from_rc(&rc, |x| match x {
    ///     Enum::Str(s) => None,
    ///     Enum::Int(i) => Some(i),
    /// });
    ///
    /// assert!(matches!(prc, Some(prc) if *prc == 5 ));
    /// ```
    #[inline]
    pub fn try_from_rc<U, F>(rc: &Rc<U>, project: F) -> Option<Self>
    where
        U: ?Sized,
        T: 'static,
        F: for<'x> FnOnce(&'x U) -> Option<&'x T>,
    {
        let projected = project(rc)?;
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const T as *mut T) };
        Some(Self {
            rc: TypeErasedRc::new(rc.clone()),
            projected,
        })
    }

    /// Constructs a new `Prc<T>` from an existing `Prc<T>` by projecting a field.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the underlying rc won't be cloned.
    ///
    /// # Example
    /// ```
    /// use pared::prc::Prc;
    /// let prc = Prc::new((5u64,));
    /// let projected = prc.project(|tuple| &tuple.0);
    /// ```
    ///
    /// Note that references to local variables cannot be returned from the `project` function:
    /// ```compile_fail
    /// use pared::prc::Prc;
    /// let prc = Prc::new((5u64,));
    /// let local = 5;
    /// let projected = prc.project(|tuple| &local);
    /// ```
    #[inline]
    pub fn project<U, F>(&self, project: F) -> Prc<U>
    where
        U: ?Sized + 'static,
        F: for<'x> FnOnce(&'x T) -> &'x U,
    {
        let projected = project(self);
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const U as *mut U) };
        Prc::<U> {
            rc: self.rc.clone(),
            projected,
        }
    }

    /// Constructs a new `Option<Prc<T>>` from an existing `Prc<T>` by trying to projecting a field.
    ///
    /// If the function passed into this returns `None`, this method will also return `None`.
    ///
    /// # Panics
    /// If `f` panics, the panic is propagated to the caller and the underlying rc won't be cloned.
    ///
    /// # Example
    /// ```
    /// use pared::prc::Prc;
    ///
    /// enum Enum {
    ///     Str(String),
    ///     Int(isize),
    /// }
    ///
    /// let prc = Prc::new(Enum::Int(5));
    /// let projected = prc.try_project(|x| match x {
    ///     Enum::Str(s) => None,
    ///     Enum::Int(i) => Some(i),
    /// });
    ///
    /// assert!(matches!(projected, Some(p) if *p == 5 ));
    /// ```
    #[inline]
    pub fn try_project<U, F>(&self, project: F) -> Option<Prc<U>>
    where
        U: ?Sized + 'static,
        F: for<'x> FnOnce(&'x T) -> Option<&'x U>,
    {
        let projected = project(self)?;
        // SAFETY: fn shouldn't be able to capture any local references
        // which should mean that the projection done by f is safe
        let projected = unsafe { NonNull::new_unchecked(projected as *const U as *mut U) };
        Some(Prc::<U> {
            rc: self.rc.clone(),
            projected,
        })
    }

    /// Provides a raw pointer to the data.
    ///
    /// The counts are not affected in any way and the `Prc` is not consumed. The pointer is valid for
    /// as long as there are strong counts in the `Prc` or in the underlying `Rc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pared::prc::Prc;
    ///
    /// let x = Prc::new("hello".to_owned());
    /// let y = Prc::clone(&x);
    /// let x_ptr = Prc::as_ptr(&x);
    /// assert_eq!(x_ptr, Prc::as_ptr(&y));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    #[must_use]
    pub fn as_ptr(this: &Self) -> *const T {
        NonNull::as_ptr(this.projected)
    }

    /// Creates a new `Weak` pointer to this allocation.
    ///
    /// This `Weak` pointer is tied to strong references to the original `Rc`, meaning it's not
    /// tied to instances of the `Prc` it was created from.
    ///
    /// # Example
    /// ```
    /// # use std::rc::Rc;
    /// use pared::prc::Prc;
    /// let rc = Rc::new((42,));
    /// let weak = {
    ///     let prc = Prc::from_rc(&rc, |tuple| &tuple.0);
    ///     Prc::downgrade(&prc)
    /// };
    /// let stored = weak.upgrade().map(|prc| *prc);
    /// assert_eq!(stored, Some(42));
    /// ```
    pub fn downgrade(this: &Prc<T>) -> Weak<T> {
        Weak::<T> {
            weak: this.rc.downgrade(),
            projected: this.projected,
        }
    }

    /// Gets the number of [`Weak`] pointers to this allocation.
    ///
    /// See [`Rc::weak_count`].
    ///
    /// # Example
    /// ```
    /// use pared::prc::Prc;
    /// let six = Prc::new(6);
    /// let _weak_six = Prc::downgrade(&six);
    ///
    /// assert_eq!(Prc::weak_count(&six), 1);
    /// ```
    ///
    /// [`Rc::weak_count`]: https://doc.rust-lang.org/std/rc/struct.Rc.html#method.weak_count
    #[inline]
    pub fn weak_count(this: &Prc<T>) -> usize {
        this.rc.weak_count()
    }

    /// Gets the number of strong pointers to this allocation.
    ///
    /// See [`Rc::strong_count`].
    ///
    /// # Example
    /// ```
    /// use pared::prc::Prc;
    /// let six = Prc::new(6);
    /// let _also_six = six.clone();
    ///
    /// assert_eq!(Prc::strong_count(&six), 2);
    /// ```
    ///
    /// [`Rc::weak_count`]: https://doc.rust-lang.org/std/rc/struct.Rc.html#method.strong_count
    #[inline]
    pub fn strong_count(this: &Prc<T>) -> usize {
        this.rc.strong_count()
    }

    /// Returns `true` if the two `Prc`s point to the same data, using [`core::ptr::eq`].
    /// See that function for caveats when comparing `dyn Trait` pointers.
    ///
    /// # Example
    /// ```
    /// use pared::prc::Prc;
    ///
    /// let five = Prc::new(5);
    /// let same_five = five.clone();
    /// let other_five = Prc::new(5);
    ///
    /// assert!(Prc::ptr_eq(&five, &same_five));
    /// assert!(!Prc::ptr_eq(&five, &other_five));
    /// ```
    ///
    /// [`core::ptr::eq`]: https://doc.rust-lang.org/core/ptr/fn.eq.html
    pub fn ptr_eq(this: &Prc<T>, other: &Prc<T>) -> bool {
        core::ptr::eq(this.projected.as_ptr(), other.projected.as_ptr())
    }
}

impl<T: ?Sized> AsRef<T> for Prc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> core::borrow::Borrow<T> for Prc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> Clone for Prc<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            rc: self.rc.clone(),
            projected: self.projected,
        }
    }
}

impl<T: ?Sized + core::fmt::Debug> core::fmt::Debug for Prc<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Prc")
            .field("projected", &self.deref())
            .finish()
    }
}

impl<T> core::fmt::Display for Prc<T>
where
    T: core::fmt::Display + ?Sized,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

#[cfg(feature = "std")]
impl<T> std::error::Error for Prc<T>
where
    T: std::error::Error + ?Sized,
{
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.deref().source()
    }
}

impl<T, F> From<F> for Prc<T>
where
    T: ?Sized + 'static,
    F: Into<Rc<T>>,
{
    #[inline]
    fn from(value: F) -> Self {
        Prc::from_rc(&value.into(), |x| x)
    }
}

impl<T> FromIterator<T> for Prc<[T]>
where
    T: 'static,
{
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().collect::<Rc<[T]>>().into()
    }
}

impl<T> Hash for Prc<T>
where
    T: Hash + ?Sized,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<T> PartialEq<Prc<T>> for Prc<T>
where
    T: PartialEq<T> + ?Sized,
{
    #[inline]
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
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let this: &T = self;
        let other: &T = other;
        this.cmp(other)
    }
}

impl<T> PartialOrd<Prc<T>> for Prc<T>
where
    T: PartialOrd<T> + ?Sized,
{
    #[inline]
    fn partial_cmp(&self, other: &Prc<T>) -> Option<core::cmp::Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T> core::fmt::Pointer for Prc<T>
where
    T: ?Sized,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Pointer::fmt(&self.projected, f)
    }
}

impl<T> Unpin for Prc<T> where T: ?Sized {}
impl<T> core::panic::UnwindSafe for Prc<T> where T: core::panic::RefUnwindSafe + ?Sized {}

/// Weak is a version of [`Prc`] that holds a non-owning reference to the managed allocation.
/// The allocation is accessed by calling [`upgrade`], which returns `Option<Prc<T>>`.
///
/// `Weak` will be valid as long as the original allocation is alive; it's not tied to the specific
/// `Prc` it was created from.
///
/// See [`std::sync::Weak`] for more details.
///
/// # Example
/// ```
/// use pared::prc::{Prc, Weak};
///
/// let tuple = Prc::new((7, 8));
/// let weak: Weak<(usize, usize)> = Prc::downgrade(&tuple);
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
/// [`std::sync::Weak`]: https://doc.rust-lang.org/std/rc/struct.Weak.html
pub struct Weak<T: ?Sized> {
    weak: TypeErasedWeak,
    projected: NonNull<T>,
}

impl<T: ?Sized> Weak<T> {
    /// Returns a raw pointer to the object `T` pointed to by this `Weak<T>`.
    ///
    /// The pointer is valid only if there are some strong references.
    ///
    /// # Examples
    ///
    /// ```
    /// use pared::prc::Prc;
    /// use std::ptr;
    ///
    /// let strong = Prc::new("hello".to_owned());
    /// let weak = Prc::downgrade(&strong);
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
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        NonNull::as_ptr(self.projected)
    }

    /// Attempts to upgrade the `Weak` pointer to a [`Prc`], delaying dropping of the inner value
    /// if successful.
    ///
    /// Returns [`None`] if the inner value has since been dropped.
    ///
    /// # Example
    /// ```
    ///
    /// use pared::prc::Prc;
    /// let five = Prc::new(5);
    ///
    /// let weak_five = Prc::downgrade(&five);
    ///
    /// let strong_five: Option<Prc<_>> = weak_five.upgrade();
    /// assert!(strong_five.is_some());
    ///
    /// // Destroy all strong pointers.
    /// drop(strong_five);
    /// drop(five);
    ///
    /// assert!(weak_five.upgrade().is_none());
    /// ```
    #[inline]
    pub fn upgrade(&self) -> Option<Prc<T>> {
        Some(Prc {
            rc: self.weak.upgrade()?,
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
    /// [`std::sync::Weak::weak_count`]: https://doc.rust-lang.org/std/rc/struct.Weak.html#method.weak_count
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
        write!(f, "(Peak)")
    }
}
