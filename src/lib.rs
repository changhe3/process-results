//! This crate facilitates processing an iterator of some `Result` type.
//! It provides the same functionality provided by
//! [`Itertools::process_results`](https://docs.rs/itertools/0.10.1/itertools/fn.process_results.html),
//! hence the name, but with a more much ergonomic interface, some extra
//! helper methods and a macro to reduce boiler-plate.   
//!
//! At a high level this crate is composed of 3 items: an extension trait [`IterResult`] that is
//! implemented for all [iterators][Iterator] of [`Result`] type, [`Fallible`] struct that
//! wraps the iterator, and [`ErrorCollector`][ErrorCollector] that stores the errors.
//!
//! [`IterResult`] is an extension trait that contains methods that consumes itself and wrap it
//! with [`Fallible`] and appropriate the error collector.
//!
//! [`Fallible`] has methods [`Fallible::process`] and [`Fallible::process_no_discard`]
//! that accept a closure, which allows the caller to process an `impl Iterator<Item = Result<T, E>>`
//! as an `impl Iterator<Item = T>` and to handle the errors in a composable manner.
//!
//! [`ErrorCollector`] is a trait that let the implementor determine how errors are stored, whether
//! or not an error shall stop the iteration, as well as how should errors be returned.  
//! Implementations are provided for common types like
//! [`Option`][ErrorCollector#impl-ErrorCollector-for-Option<E>]
//! and [`Vec`][ErrorCollector#impl-ErrorCollector-for-Vec<E>] to allow the iteration to stop and
//! return the first error encountered and return, or to finish the iteration and stop all errors
//! in a [`Vec`]. Unit struct [`Ignore`] is also provided that ignores all the errors encountered.
//!
//! # Examples
//!
//! ### Simple Iteration
//! ```
//! use process_results::IterResult;
//!
//! let v = vec![Ok(1i64), Ok(4), Ok(-3), Err("Error"), Ok(10)];
//! let res: Result<i64, _> = v.into_iter().failfast().process(|it| it.sum());
//! assert_eq!(res, Err("Error"));
//! ```
//!
//! ### Accumulate Errors
//! ```
//! use process_results::IterResult;
//!
//! let v = vec![
//!     Ok(1i64),
//!     Err("Error1"),
//!     Ok(4),
//!     Ok(-3),
//!     Err("Error2"),
//!     Ok(10),
//! ];
//! let res: Result<i64, _> = v
//!     .into_iter()
//!     .accumulate()
//!     .process(|it| it.sum());
//! assert_eq!(res, Err(vec!["Error1", "Error2"]));
//! ```
//!
//! ### Nested Errors
//! Here is an example that read lines from files in a folder, parse each line as `i32`
//! while saving the lines that cannot be parsed successfully.
//!
//! ```
//! use process_results::*;
//! use process_results::fallible;
//! use std::path::Path;
//! use std::fs::File;
//! use std::io::BufReader;
//! use std::io::BufRead;
//!
//! let res_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("res");
//! let res_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("res");
//! let (sum, err) = res_dir
//!     .read_dir()
//!     .unwrap()
//!     .failfast()
//!     .process(|it| {
//!         it.filter(|entry| entry.file_type().map_or(false, |t| t.is_file()))
//!             .map(|entry| {
//!                 File::open(entry.path())
//!                     .map(BufReader::new)
//!                     .map(|f| (entry.file_name(), f))
//!             })
//!             .failfast()
//!             .process(|it| {
//!                 it.flat_map(|(name, f)| {
//!                     f.lines()
//!                         .enumerate()
//!                         .map(move |(ln_no, ln)| ln.map(|ln| (name.clone(), ln_no, ln)))
//!                 })
//!                 .failfast()
//!                 .process(|it| {
//!                     it.map(|(name, ln_no, ln)| {
//!                         ln.parse::<i32>().map_err(|_e| {
//!                             format!("{}-{}: {}", name.to_string_lossy(), ln_no + 1, ln)
//!                         })
//!                     })
//!                     .accumulate()
//!                     .process_no_discard::<_, i32>(|it| it.sum())
//!                 })
//!             })
//!     })
//!     .unwrap()
//!     .unwrap()
//!     .unwrap();
//! assert_eq!(sum, 11966);
//! assert_eq!(
//!     err.unwrap(),
//!     vec![
//!         "test1.txt-7: sadfs",
//!         "test2.txt-3: 1000000000000000000000000000000000000000000000000000000000",
//!         "test2.txt-6: hello world",
//!         "test2.txt-8: 1.35"
//!     ]
//! );
//! ```
//!
//!
//! ### Nested Errors with Macro
//! The same code as the last one, but utilizing macro [`fallible!`].
//!
//! ```
//! use process_results::*;
//! use process_results::fallible;
//! use std::path::Path;
//! use std::fs::File;
//! use std::io::BufReader;
//! use std::io::BufRead;
//!
//! let res_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("res");
//! let (sum, err) = fallible!(
//!     res_dir.read_dir().unwrap().failfast(),
//!     |it| it
//!         .filter(|entry| entry.file_type().map_or(false, |t| t.is_file()))
//!         .map(|entry| File::open(entry.path()).map(BufReader::new)
//!         .map(|f| (entry.file_name(), f))).failfast(),
//!     |it| it.flat_map(
//!         |(name, f)| f.lines()
//!             .enumerate()
//!             .map(move |(ln_no, ln)| ln.map(|ln| (name.clone(), ln_no, ln)))
//!     ).failfast(),
//!     |it| it
//!         .map(
//!             |(name, ln_no, ln)| ln.parse::<i32>()
//!                 .map_err(|_e| format!("{}-{}: {}", name.to_string_lossy(), ln_no + 1, ln))
//!         )
//!         .accumulate(),
//!     no_discard i32: |it| it.sum()
//! ).unwrap().unwrap().unwrap();
//! assert_eq!(sum, 11966);
//! assert_eq!(
//!     err.unwrap(),
//!     vec![
//!         "test1.txt-7: sadfs",
//!         "test2.txt-3: 1000000000000000000000000000000000000000000000000000000000",
//!         "test2.txt-6: hello world",
//!         "test2.txt-8: 1.35"
//!     ]
//! );
//! ```

use crate::errors::Ignore;
use crate::raw_iter::RawIter;
use errors::ErrorCollector;

pub mod errors;
pub mod raw_iter;

/// An extension trait implemented for all iterators of `Result` types.  
pub trait IterResult: Iterator<Item = Result<Self::Ok, Self::Error>> + Sized {
    /// The type wrapped by the `Ok` variant of the `Result` type
    type Ok;
    /// The type wrapped by the `Err` variant of the `Result` type
    type Error;

    /// Produces a version of [`Fallible`] that stops iterating upon encountering the 1st error.
    #[inline]
    fn failfast(self) -> Fallible<Self, Option<Self::Error>> {
        self.fallible()
    }

    /// Produces a version of [`Fallible`] that keeps iterating and ignores all errors.
    #[inline]
    fn ignore(self) -> Fallible<Self, Ignore> {
        self.fallible()
    }

    /// Produces a version of [`Fallible`] that keeps iterating and stores all errors in a `Vec`.
    #[inline]
    fn accumulate(self) -> Fallible<Self, Vec<Self::Error>> {
        self.fallible()
    }

    /// Produces a version of [`Fallible`] with a custom type of [`ErrorCollector`]
    #[inline]
    fn fallible<C: ErrorCollector<Self::Error>>(self) -> Fallible<Self, C> {
        self.with_collector(C::empty())
    }

    /// Produces a version of [`Fallible`] with an existing value of [`ErrorCollector`]
    #[inline]
    fn with_collector<C: ErrorCollector<Self::Error>>(self, collector: C) -> Fallible<Self, C> {
        Fallible {
            iter: self,
            errors: collector,
        }
    }
}

impl<I, T, E> IterResult for I
where
    I: Iterator<Item = Result<T, E>>,
{
    type Ok = T;
    type Error = E;
}

#[derive(Debug, Clone)]
pub struct Fallible<I, C> {
    iter: I,
    errors: C,
}

#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
impl<I, C> Fallible<I, C>
where
    I: IterResult,
    C: ErrorCollector<I::Error>,
{
    /// “Lift” a function of the values of an iterator so that it can process an iterator of [`Result`]
    /// values instead.
    // fixme: I really don't know how to word this in a better way.
    ///
    /// `f` is a closure that takes [`RawIter`], an iterator adapter that wraps the inner
    /// iterator and implements `Iterator<Item=I::OK>`.
    ///
    /// Returns either the returned value of closure `f` wrapped in the `Ok` variant, or the error
    /// wrapped in `Err` variant, in a way specified by `C`'s implementation of [`ErrorCollector`].
    #[inline]
    pub fn process<F, B>(self, f: F) -> Result<B, C::Collection>
    where
        F: FnOnce(RawIter<I, C>) -> B,
    {
        let Self { iter, mut errors } = self;
        let raw_iter = RawIter {
            iter,
            errors: &mut errors,
        };
        let b = f(raw_iter);
        errors.with_value(b)
    }

    /// “Lift” a function of the values of an iterator so that it can process an iterator of [`Result`]
    /// values instead.
    // fixme: I really don't know how to word this in a better way.
    ///
    /// `f` is a closure that takes [`RawIter`], an iterator adapter that wraps the inner
    /// iterator and implements `Iterator<Item=I::OK>`.
    ///
    /// Returns both the returned value of closure `f` and None if the wrapped iterator runs to
    /// completion; otherwise, returns the intermediate value produced so far and the errors in a
    /// way specified by `C`'s implementation of [`ErrorCollector`]
    #[inline]
    pub fn process_no_discard<F, B>(self, f: F) -> (B, Option<C::Collection>)
    where
        F: FnOnce(RawIter<I, C>) -> B,
    {
        let Self { iter, mut errors } = self;
        let raw_iter = RawIter {
            iter,
            errors: &mut errors,
        };
        let b = f(raw_iter);
        (b, errors.with_value(()).err())
    }
}

/// A macro used to reduce boilerplate when nesting multiple calls to [`process`][Fallible::process]
/// or [`process_no_discard`][Fallible::process_no_discard] inside each other.
///
/// [`Fallible`] and [`IterResult`] must be imported to use the macro.
#[macro_export]
macro_rules! fallible {
    ($base:expr) => {
        $base
    };
    ($base:expr, $($b_type:ty :)? | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        Fallible::process$(::<_, $b_type>)?($base, |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
    ($base:expr, $($b_type:ty :)? move | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        Fallible::process$(::<_, $b_type>)?($base, move |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
    ($base:expr, no_discard $($b_type:ty :)? | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        Fallible::process_no_discard$(::<_, $b_type>)?($base, |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
    ($base:expr, no_discard $($b_type:ty :)? move | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        Fallible::process_no_discard$(::<_, $b_type>)?($base, move |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
}

#[cfg(test)]
mod tests {
    use crate::Fallible;
    use crate::IterResult;
    use std::fs::File;
    use std::io::{BufRead, BufReader};
    use std::path::Path;

    #[test]
    fn test_failfast() {
        let v = vec![Ok(1i64), Ok(4), Ok(-3), Err("Error"), Ok(10)];
        let res: Result<i64, _> = v.into_iter().failfast().process(|it| it.sum());
        assert_eq!(res, Err("Error"));
    }

    #[test]
    fn test_success() {
        let v: Vec<Result<_, &str>> = vec![Ok(1i64), Ok(4), Ok(-3), Ok(10)];
        let res: i64 = v
            .iter()
            .map(Result::as_ref)
            .failfast()
            .process(|it| it.sum())
            .unwrap();
        assert_eq!(res, 12);
    }

    #[test]
    fn test_filter() {
        let v = vec![Ok(1i64), Ok(4), Ok(-3), Err("Error"), Ok(10)];
        let res: i64 = v.into_iter().ignore().process(|it| it.sum()).unwrap();
        assert_eq!(res, 12);
    }

    #[test]
    fn test_accumulator() {
        let v = vec![
            Ok(1i64),
            Err("Error1"),
            Ok(4),
            Ok(-3),
            Err("Error2"),
            Ok(10),
        ];
        let res: Result<i64, _> = v
            .into_iter()
            .with_collector(Vec::new())
            .process(|it| it.sum());
        assert_eq!(res, Err(vec!["Error1", "Error2"]));
    }

    #[test]
    fn test_recursive() -> eyre::Result<()> {
        let res_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("res");
        let sum = res_dir.read_dir()?.failfast().process(|it| {
            it.filter(|entry| entry.file_type().map_or(false, |t| t.is_file()))
                .map(|entry| File::open(entry.path()))
                .failfast()
                .process(|it| {
                    it.map(BufReader::new)
                        .flat_map(|f| f.lines())
                        .failfast()
                        .process(|it| {
                            it.map(|ln| ln.parse::<i32>())
                                .ignore()
                                .process::<_, i32>(|it| it.sum())
                        })
                })
        })????;
        assert_eq!(sum, 11966);
        Ok(())
    }

    #[test]
    fn test_macro() -> eyre::Result<()> {
        let res_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("res");
        let (sum, err) = fallible!(
            res_dir.read_dir()?.failfast(),
            |it| it
                .filter(|entry| entry.file_type().map_or(false, |t| t.is_file()))
                .map(|entry| File::open(entry.path()).map(BufReader::new)
                .map(|f| (entry.file_name(), f))).failfast(),
            |it| it.flat_map(
                |(name, f)| f.lines()
                    .enumerate()
                    .map(move |(ln_no, ln)| ln.map(|ln| (name.clone(), ln_no, ln)))
            ).failfast(),
            |it| it
                .map(
                    |(name, ln_no, ln)| ln.parse::<i32>()
                        .map_err(|_e| format!("{}-{}: {}", name.to_string_lossy(), ln_no + 1, ln))
                )
                .accumulate(),
            no_discard i32: |it| it.sum()
        )???;
        assert_eq!(sum, 11966);
        assert_eq!(
            err.unwrap(),
            vec![
                "test1.txt-7: sadfs",
                "test2.txt-3: 1000000000000000000000000000000000000000000000000000000000",
                "test2.txt-6: hello world",
                "test2.txt-8: 1.35"
            ]
        );
        Ok(())
    }
}
