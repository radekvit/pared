#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

use pared::sync::{Parc, Weak};
use std::any::Any;
use std::cmp::PartialEq;
use std::error::Error;
use std::sync::{Arc, Mutex};

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn slice() {
    let a: Parc<[u32; 3]> = Arc::new([3, 2, 1]).into();
    let b: Parc<[u32]> = a.project(|x| &x[..]); // Conversion
    assert_eq!(*a, *b);

    // Exercise is_dangling() with a DST
    let mut a: Weak<[u32]> = Parc::downgrade(&b);
    a = a.clone();
    assert!(a.upgrade().is_some());
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn trait_object() {
    let a: Parc<u32> = Parc::new(4);
    let a: Parc<dyn Any> = a.project(|x| x as &dyn Any); // Unsizing

    // Exercise is_dangling() with a DST
    let mut a = Parc::downgrade(&a);
    a = a.clone();
    assert!(a.upgrade().is_some());
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn float_nan_ne() {
    #![allow(clippy::eq_op)]
    let x = Parc::new(f32::NAN);
    assert!(x != x);
    assert!(!(x == x));
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn partial_eq() {
    #![allow(clippy::eq_op)]
    #![allow(clippy::mutex_atomic)]

    struct TestPEq(Mutex<usize>);
    impl PartialEq for TestPEq {
        fn eq(&self, other: &TestPEq) -> bool {
            *self.0.lock().unwrap() += 1;
            *other.0.lock().unwrap() += 1;
            true
        }
    }
    let x = Parc::new(TestPEq(Mutex::new(0)));
    assert!(x == x);
    assert!(!(x != x));
    assert_eq!(*x.0.lock().unwrap(), 4);
}

const SHARED_ITER_MAX: u16 = 100;

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn shared_from_iter_normal() {
    #![allow(clippy::redundant_clone)]
    // Exercise the base implementation for non-`TrustedLen` iterators.
    {
        // `Filter` is never `TrustedLen` since we don't
        // know statically how many elements will be kept:
        let iter = (0..SHARED_ITER_MAX).filter(|x| x % 2 == 0).map(Box::new);

        // Collecting into a `Vec<T>` or `Parc<[T]>` should make no difference:
        let vec = iter.clone().collect::<Vec<_>>();
        let parc = iter.collect::<Parc<[_]>>();
        assert_eq!(&*vec, &*parc);

        // Clone a bit and let these get dropped.
        {
            let _parc_2 = parc.clone();
            let _parc_3 = parc.clone();
            let _parc_4 = Parc::downgrade(&_parc_3);
        }
    } // Drop what hasn't been here.
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn projection_to_member() {
    #![allow(clippy::mutex_atomic)]
    struct HasMembers {
        _unused: usize,
        a: Mutex<usize>,
    }
    let parc = Parc::new(HasMembers {
        _unused: 64,
        a: Mutex::new(432),
    });
    let projected = parc.project(|s| &s.a);

    assert_eq!(*projected.lock().unwrap(), 432);

    *parc.a.lock().unwrap() = 15;
    assert_eq!(*projected.lock().unwrap(), 15);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn projection_of_dyn() {
    struct HasMembers {
        s: String,
    }
    let parc = Parc::new(HasMembers {
        s: String::from("Hello!"),
    });
    let projected: Parc<dyn std::fmt::Display> = parc.project(|s| &s.s as &dyn std::fmt::Display);

    let formatted = format!("{}", projected);

    assert_eq!(formatted, "Hello!");
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn fallible_projections() {
    enum Test {
        A(String),
        B,
    }

    fn try_project(t: &Test) -> Result<&str, ()> {
        match t {
            Test::A(s) => Ok(s),
            Test::B => Err(()),
        }
    }

    let arc = Arc::new(Test::B);
    let parc = Parc::try_from_arc(&arc, try_project);
    assert!(parc.is_err());

    let parc = Parc::new(Test::B);
    let parc = parc.try_project(try_project);
    assert!(parc.is_err());

    let arc = Arc::new(Test::A("Hi!".to_owned()));
    let parc = Parc::try_from_arc(&arc, try_project);
    assert!(matches!(parc, Ok(p) if &*p == "Hi!"));

    let parc = Parc::new(Test::A("Hi!".to_owned()));
    let parc = parc.try_project(try_project);
    assert!(matches!(parc, Ok(p) if &*p == "Hi!"));
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn as_ptr() {
    #[repr(C)]
    struct Test {
        _b: bool,
        a: i32,
    }
    let rc = Arc::new(Test { a: 1, _b: true });
    let parc = Parc::from_arc(&rc, |x| &x.a);
    let weak = Parc::downgrade(&parc);

    assert!(Parc::as_ptr(&parc) == &rc.a as *const i32);
    assert!(Weak::as_ptr(&weak) == &rc.a as *const i32);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn counts() {
    let parc = Parc::new(5);
    let parc2 = parc.clone();

    assert_eq!(Parc::weak_count(&parc), 0);
    assert_eq!(Parc::strong_count(&parc), 2);
    assert_eq!(Parc::strong_count(&parc2), 2);

    let weak = Parc::downgrade(&parc);
    assert_eq!(Weak::weak_count(&weak), 1);
    assert_eq!(Weak::strong_count(&weak), 2);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn ptr_eq() {
    let parc = Parc::new(5);
    let cloned = parc.clone();
    let parc2 = Parc::new(5);

    assert!(Parc::ptr_eq(&parc, &cloned));
    assert!(!Parc::ptr_eq(&parc, &parc2));

    let weak = Parc::downgrade(&parc);
    let weak_cloned = Parc::downgrade(&parc);
    let weak2 = Parc::downgrade(&parc2);

    assert!(Weak::ptr_eq(&weak, &weak_cloned));
    assert!(!Weak::ptr_eq(&weak, &weak2));
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn borrows() {
    let parc = Parc::new(5);

    let _ = parc.as_ref();
    let _: &i32 = std::borrow::Borrow::borrow(&parc);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn fmt() {
    let parc = Parc::new(5);

    format!("{} {:?} {:p}", parc, parc, parc);

    let weak = Parc::downgrade(&parc);

    format!("{:?}", weak);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn errors() {
    use std::io::{Error, ErrorKind};

    let parc = Parc::new(Error::new(ErrorKind::AddrInUse, ""));

    let _ = parc.source();
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn hash() {
    use std::collections::HashMap;

    let parc = Parc::new(5);

    let mut hm = HashMap::new();
    hm.insert(parc, 1);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn cmp() {
    let five = Parc::new(5);
    let six = Parc::new(6);

    assert_eq!(five.cmp(&six), std::cmp::Ordering::Less);
    assert_eq!(five.partial_cmp(&six), Some(std::cmp::Ordering::Less));
}
