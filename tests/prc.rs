#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

use pared::prc::{Prc, Weak};
use std::any::Any;
use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::error::Error;
use std::rc::Rc;

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn slice() {
    let a: Prc<[u32; 3]> = Rc::new([3, 2, 1]).into();
    let b: Prc<[u32]> = a.project(|x| &x[..]); // Conversion
    assert_eq!(*a, *b);

    // Exercise is_dangling() with a DST
    let mut a = Prc::downgrade(&b);
    a = a.clone();
    assert!(a.upgrade().is_some());
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn trait_object() {
    let a: Prc<u32> = Prc::new(4);
    let a: Prc<dyn Any> = a.project(|x| x as &dyn Any); // Unsizing

    // Exercise is_dangling() with a DST
    let mut a = Prc::downgrade(&a);
    a = a.clone();
    assert!(a.upgrade().is_some());
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn float_nan_ne() {
    #![allow(clippy::eq_op)]

    let x = Prc::new(f32::NAN);
    assert!(x != x);
    assert!(!(x == x));
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn partial_eq() {
    #![allow(clippy::eq_op)]

    struct TestPEq(RefCell<usize>);
    impl PartialEq for TestPEq {
        fn eq(&self, other: &TestPEq) -> bool {
            *self.0.borrow_mut() += 1;
            *other.0.borrow_mut() += 1;
            true
        }
    }
    let x = Prc::new(TestPEq(RefCell::new(0)));
    assert!(x == x);
    assert!(!(x != x));
    assert_eq!(*x.0.borrow(), 4);
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

        // Collecting into a `Vec<T>` or `Prc<[T]>` should make no difference:
        let vec = iter.clone().collect::<Vec<_>>();
        let prc = iter.collect::<Prc<[_]>>();
        assert_eq!(&*vec, &*prc);

        // Clone a bit and let these get dropped.
        {
            let _prc_2 = prc.clone();
            let _prc_3 = prc.clone();
            let _prc_4 = Prc::downgrade(&_prc_3);
        }
    } // Drop what hasn't been here.
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn projection_to_member() {
    struct HasMembers {
        _unused: usize,
        a: RefCell<usize>,
    }
    let prc = Prc::new(HasMembers {
        _unused: 64,
        a: RefCell::new(432),
    });
    let projected = prc.project(|s| &s.a);

    assert_eq!(*projected.borrow(), 432);

    *prc.a.borrow_mut() = 15;
    assert_eq!(*projected.borrow(), 15);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn projection_of_dyn() {
    struct HasMembers {
        s: String,
    }
    let prc = Prc::new(HasMembers {
        s: String::from("Hello!"),
    });
    let projected: Prc<dyn std::fmt::Display> = prc.project(|s| &s.s as &dyn std::fmt::Display);

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

    fn try_project(t: &Test) -> Option<&str> {
        match t {
            Test::A(s) => Some(s),
            Test::B => None,
        }
    }

    let rc = Rc::new(Test::B);
    let prc = Prc::try_from_rc(&rc, try_project);
    assert!(prc.is_none());

    let prc = Prc::new(Test::B);
    let prc = prc.try_project(try_project);
    assert!(prc.is_none());

    let rc = Rc::new(Test::A("Hi!".to_owned()));
    let prc = Prc::try_from_rc(&rc, try_project);
    assert!(matches!(prc, Some(p) if &*p == "Hi!"));

    let prc = Prc::new(Test::A("Hi!".to_owned()));
    let prc = prc.try_project(try_project);
    assert!(matches!(prc, Some(p) if &*p == "Hi!"));
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn as_ptr() {
    #[repr(C)]
    struct Test {
        _b: bool,
        a: i32,
    }
    let rc = Rc::new(Test { a: 1, _b: true });
    let prc = Prc::from_rc(&rc, |x| &x.a);
    let weak = Prc::downgrade(&prc);

    assert!(Prc::as_ptr(&prc) == &rc.a as *const i32);
    assert!(Weak::as_ptr(&weak) == &rc.a as *const i32);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn counts() {
    let prc = Prc::new(5);
    let prc2 = prc.clone();

    assert_eq!(Prc::weak_count(&prc), 0);
    assert_eq!(Prc::strong_count(&prc), 2);
    assert_eq!(Prc::strong_count(&prc2), 2);

    let weak = Prc::downgrade(&prc);
    assert_eq!(Weak::weak_count(&weak), 1);
    assert_eq!(Weak::strong_count(&weak), 2);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn ptr_eq() {
    let prc = Prc::new(5);
    let cloned = prc.clone();
    let prc2 = Prc::new(5);

    assert!(Prc::ptr_eq(&prc, &cloned));
    assert!(!Prc::ptr_eq(&prc, &prc2));

    let weak = Prc::downgrade(&prc);
    let weak_cloned = Prc::downgrade(&prc);
    let weak2 = Prc::downgrade(&prc2);

    assert!(Weak::ptr_eq(&weak, &weak_cloned));
    assert!(!Weak::ptr_eq(&weak, &weak2));
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn borrows() {
    let prc = Prc::new(5);

    let _ = prc.as_ref();
    let _: &i32 = std::borrow::Borrow::borrow(&prc);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn fmt() {
    let prc = Prc::new(5);

    format!("{} {:?} {:p}", prc, prc, prc);

    let weak = Prc::downgrade(&prc);

    format!("{:?}", weak);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn errors() {
    use std::io::{Error, ErrorKind};

    let prc = Prc::new(Error::new(ErrorKind::AddrInUse, ""));

    let _ = prc.source();
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn hash() {
    let prc = Prc::new(5);

    let mut hm = HashMap::new();
    hm.insert(prc, 1);
}

#[test]
#[cfg_attr(coverage_nightly, coverage(off))]
fn cmp() {
    let five = Prc::new(5);
    let six = Prc::new(6);

    assert_eq!(five.cmp(&six), std::cmp::Ordering::Less);
    assert_eq!(five.partial_cmp(&six), Some(std::cmp::Ordering::Less));
}
