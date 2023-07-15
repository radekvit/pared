use prc::prc::Prc;
use std::any::Any;
use std::cell::RefCell;
use std::cmp::PartialEq;
use std::rc::Rc;

#[test]
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
fn trait_object() {
    let a: Prc<u32> = Prc::new(4);
    let a: Prc<dyn Any> = a.project(|x| x); // Unsizing

    // Exercise is_dangling() with a DST
    let mut a = Prc::downgrade(&a);
    a = a.clone();
    assert!(a.upgrade().is_some());
}

#[test]
fn float_nan_ne() {
    let x = Prc::new(f32::NAN);
    assert!(x != x);
    assert!(!(x == x));
}

#[test]
fn partial_eq() {
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
fn shared_from_iter_normal() {
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
fn projection_of_dyn() {
    struct HasMembers {
        s: String,
    }
    let prc = Prc::new(HasMembers {
        s: String::from("Hello!"),
    });
    let projected: Prc<dyn std::fmt::Display> = prc.project(|s| &s.s);

    let formatted = format!("{}", projected);

    assert_eq!(formatted, "Hello!");
}
