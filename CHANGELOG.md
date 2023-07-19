# Changelog

## 0.2.2
- Switch `TypeErasedArc` and `TypeErasedRc` to use `ManuallyDrop` when converting the raw pointer into a concrete `Arc<T>`, `Rc<T>` or `Weak<T>` to avoid incorrect behavior in case any method we call panics. Previously, the temporary would be dropped even if it shouldn't have, causing potential UB (use after free).
- Add `Prc::try_from_rc`, `Prc::try_project`, `Parc::try_from_arc`, and `Parc::try_project`. These are fallible versions of the same methods without `try_`, where the `FnOnce` that's passed to these functions returns an `Option`. This allows for using `Prc` and `Parc` where the projected reference might be unavailable.

## 0.2.1
- Fix incorrect lifetime bounds on `Prc::from_rc` and `Parc::from_arc`.

## 0.2.0
- Fix the soundness issue from 0.1.0 by requiring that any `T` returned by any projecting function is `T: 'static`. This change technically restricts the types we can use with `Prc` and `Parc`, but doesn't interfere with any intended usage of the crate.

*(yanked due to flipped bounds on `project` functions causing a soundness hole)*

## 0.1.0
Initial release.

*(yanked due to a soundness hole where it was possible to use a reference to a reference that didn't live long enough)*