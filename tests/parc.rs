use pared::sync::{Parc, Weak};
use std::any::Any;
use std::cmp::PartialEq;
use std::sync::{Arc, Mutex};

#[test]
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
fn trait_object() {
    let a: Parc<u32> = Parc::new(4);
    let a: Parc<dyn Any> = a.project(|x| x as &dyn Any); // Unsizing

    // Exercise is_dangling() with a DST
    let mut a = Parc::downgrade(&a);
    a = a.clone();
    assert!(a.upgrade().is_some());
}

#[test]
fn float_nan_ne() {
    #![allow(clippy::eq_op)]
    let x = Parc::new(f32::NAN);
    assert!(x != x);
    assert!(!(x == x));
}

#[test]
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
