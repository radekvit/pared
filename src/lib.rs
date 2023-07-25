#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

//! # `pared`
//! Reference-counted pointers that contain projections of data stored in [`std::sync::Arc`]
//! or [`std::rc::Rc`].
//! This is a "self-referential" type in the vein of [ouroboros](https://lib.rs/ouroboros)
//! or [yoke](https://lib.rs/yoke).
//!
//! This crate specializes to only supporting `Arc` and `Rc` and only references to fields
//! obtainable from them, which allows it to provide a much simpler API compared to general
//! self-referential crates.
//!
//! Parc can be useful in situations where we want to expose only a part of data stored
//! in a reference-counted pointer while still retaining the same shared ownership of that data.
//! We project a field from our stored data to store in Parc, allowing us to only expose that data
//! to the receiver.
//!
//! # Example
//! ```
//! use std::sync::Arc;
//! use pared::sync::Parc;
//!
//! fn accepts_parc(parc: Parc<u8>) {}
//!
//! // Parc can be created by projecting references from an Arc
//! let from_tuple = Parc::from_arc(&Arc::new((16usize, 8u8)), |tuple| &tuple.1);
//! // Or by using any T: Into<Arc<_>>
//! let from_u8: Parc<_> = Parc::new(8u8);
//!
//! // Functions accept any Parc<T>, regardless of which Arc<U> it was created from
//! if (true) {
//!     accepts_parc(from_tuple);
//! } else {
//!     accepts_parc(from_u8);
//! }
//! ```

#![deny(missing_docs)]
#![deny(clippy::std_instead_of_core)]
#![deny(clippy::std_instead_of_alloc)]

extern crate alloc;
extern crate core;

#[cfg(doctest)]
doc_comment::doctest!("../README.md");

pub mod prc;
pub mod sync;

mod erased_ptr;
