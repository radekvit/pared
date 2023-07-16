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

## License

&copy; 2023 Radek Vít [radekvitr@gmail.com].

This project is licensed under either of

- [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0) ([`LICENSE-APACHE`](LICENSE-APACHE))
- [MIT license](https://opensource.org/licenses/MIT) ([`LICENSE-MIT`](LICENSE-MIT))

at your option.

The [SPDX](https://spdx.dev) license identifier for this project is `MIT OR Apache-2.0`.