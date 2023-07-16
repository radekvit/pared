# pared: ***P***rojected Sh***ared*** pointers
[<img alt="License" src="https://img.shields.io/badge/license-MIT%2FApache--2.0-informational?style=flat-square" height="20">](COPYRIGHT.md)
[<img alt="crates.io" src="https://img.shields.io/crates/v/pared.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/pared)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-pared-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs" height="20">](https://docs.rs/pared)

Projections for Arc<T> and Rc<T> that allow exposing only references that come from T.

Reference-counted pointers that contain projections of data stored in [`std::sync::Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html)
or [`std::rc::Rc`](https://doc.rust-lang.org/std/rc/struct.Rc.html).
This is a "self-referential" type in the vein of [ouroboros](https://lib.rs/ouroboros)
or [yoke](https://lib.rs/yoke).
This crate specializes to only supporting `Arc` and `Rc` and only references to fields
obtainable from them, which allows it to provide a much simpler API compared to general
self-referential crates.
Parc can be useful in situations where we want to expose only a part of data stored
in a reference-counted pointer while still retaining the same shared ownership of that data.
We project a field from our stored data to store in Parc, allowing us to only expose that data
to the receiver.

This crate can be used in `no_std` environments, given that `alloc` is available.

## Usage
Pointers from this library can be useful in situations where you're required to share ownership of
data (e.g. when sending it between threads), but only want to expose a part of the stored data
to a part of the code.

```rust
use pared::sync::Parc;

#[derive(Debug)]
struct PublicData;
// No Debug
struct SensitiveData;

struct Data {
    public: PublicData,
    sensitive: SensitiveData,
}

let data = Parc::new(Data { public: PublicData, sensitive: SensitiveData });
let public_only = data.project(|data| &data.public);

std::thread::spawn(move ||
    println!("I can only access public data: {:?}", public_only)
).join().unwrap();
```

When using `Parc<T>` or `Prc<T>`, the underlying `Arc<U>` or `Rc<U>` is type-erased, so you can use instances of these pointers interchangeably:
```rust
use pared::sync::Parc;

let use_second = true;
let from_tuple = Parc::new((0u8, 1u8, 2u8)).project(|tuple|
    if use_second {
        &tuple.1
    } else {
        &tuple.0
    }
);
let from_u8 = Parc::new(4u8);

fn check_equal(number: Parc<u8>, reference: u8) {
    assert_eq!(*number, reference);
}

let use_from_tuple = true;
if use_from_tuple {
    check_equal(from_tuple, 1);
} else {
    check_equal(from_u8, 4);
}
```

## Background
C++'s [std::shared_ptr](https://en.cppreference.com/w/cpp/memory/shared_ptr) has an 
[aliasing constructor (8)](https://en.cppreference.com/w/cpp/memory/shared_ptr/shared_ptr)
that lets you reuse the existing reference count of that shared pointer, but point to
new data.
This operation is unsafe, since C++ doesn't have a way to restrict you from using this constructor
with a pointer to a local variable.

With Rust, we can expose the same operation with a safe API.
Rust's [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html) doesn't store two discinct
pointers to the reference count and the data, so it doesn't include this functionality
out of the box.

We can implement this "aliasing Arc" as a wrapper type around `Arc` (and `Rc`).
Since we're not interested in the original data stored in the `Arc`, we can type-erase the Arc
into an opaque pointer, and we only need to be able to call member functions that don't depend
on the original `T`:
- clone (to increment the counter)
- drop (to decrement the counter)
- downgrade (to get the `Weak` pointer)
- strong_count and weak_count

Similarly, for `Weak`, we only need
- clone (to increment the weak counter)
- drop (to decrement the weak counter)
- upgrade (to get `Option<Arc>`)
- strong_count and weak_count

Our wrapper types `sync::Parc`, `sync::Weak`, `prc::Prc` and `prc::Weak` store type-erased versions of their respective underlying shared pointers, which allows us to call these methods
on the underlying `Arc`s, `Rc`s and `Weak`s.

When we construct the type-erased versions of `Arc`, `Rc`, etc., we store a reference to a `const` structure with function pointers to each of those operations. Since we always construct from a concrete `Arc<T>` or `Rc<T>`, we can store a reference to a generic helper type's `const` variable that first converts the type-erased pointer back to `Arc<T>`, `Rc<T>`, or the correct `Weak<T>`, and then calls the appropriate function.

We store the underlying pointer as a pointer we obtain from
[`Arc::into_raw`](https://doc.rust-lang.org/std/sync/struct.Arc.html#method.into_raw)
or
[`Rc::into_raw`](https://doc.rust-lang.org/std/rc/struct.Rc.html#method.into_raw)
in a structure that stores this (potentially `?Sized`) pointer in a
`MaybeUninit<[*const ();2]>` (credit to [Alice Ryhl](https://users.rust-lang.org/u/alice)
from the [forum](https://users.rust-lang.org)).
This allows us to transparently store this pointer and retreive it back inside the concrete implementation functions.

As an aside, "prc" is the sound of farting in Czech, similar to "toot" in English.
This is around 20% of the motivation behind the naming convention for `Parc` and `Prc`.

## Alternatives
If this kind of projection is too simple (e.g. you'd like to store a subset of a `struct`'s pointers instead of just one), [yoke](https://lib.rs/yoke) should do the trick for `T: Sized` types.

## Acknowledgments
- [Christopher Durham](https://users.rust-lang.org/u/cad97/summary) for
[giving information](https://users.rust-lang.org/t/could-arc-have-arc-aliased-that-would-behave-like-c-shared-ptrs-aliasing-constructor/96924/5)
about prior art and outlining issues with first drafts
- [Alice Ryhl](https://users.rust-lang.org/u/alice) for
[solving](https://users.rust-lang.org/t/type-erasing-pointers-to-t-sized/96984/3)
how to transparently store pointers to `?Sized` types
- [Frank Stefahn](https://users.rust-lang.org/u/steffahn) for reviewing the original API ideas
and spotting a difficult-to-spot soundness hole with `Debug`

## License

&copy; 2023 Radek Vít [radekvitr@gmail.com].

This project is licensed under either of

- [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0) ([`LICENSE-APACHE`](LICENSE-APACHE))
- [MIT license](https://opensource.org/licenses/MIT) ([`LICENSE-MIT`](LICENSE-MIT))

at your option.

The [SPDX](https://spdx.dev) license identifier for this project is `MIT OR Apache-2.0`.