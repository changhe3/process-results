use ControlFlow::*;

/// Denotes whether the iteration should continue or not.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ControlFlow {
    /// To stop the iteration and return the error
    Break,
    /// To continue the iteration
    Continue,
}

/// Determines the manner in which the encountered error(s) are processed, stored and returned, as well as
/// whether the iteration should continue or not.
pub trait ErrorCollector {
    /// The error type to be processed
    type Error; // todo: refactor to generic parameter
    /// The type to be returned after the iteration has been stopped
    type Collection;

    /// Creates an empty `ErrorCollector`.
    fn empty() -> Self;

    /// Processes an error. Returns an [`ControlFlow`] type indicating whether the iteration shall stop
    /// or not.
    fn push_err(&mut self, err: Self::Error) -> ControlFlow;

    /// Returns `Ok(val)` if the iteration run to completion, or an error collection of type
    /// [`Self::Collection`][ErrorCollector::Collection] if error(s) were encountered.
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection>;
}

/// A unit type that implements [`ErrorCollector`]. Ignores all errors and runs the iterator to
/// completion
#[derive(Debug, Copy, Clone)]
pub struct Ignore<E>(PhantomData<E>);

impl<E> Default for Ignore<E> {
    #[inline]
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<E> ErrorCollector for Ignore<E> {
    type Error = E;
    type Collection = Infallible;

    #[inline]
    fn empty() -> Self {
        Self::default()
    }

    #[inline]
    fn push_err(&mut self, _err: Self::Error) -> ControlFlow {
        Continue
    }

    #[inline]
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection> {
        Ok(val)
    }
}

impl<E> ErrorCollector for Result<(), E> {
    type Error = E;
    type Collection = E;

    #[inline]
    fn empty() -> Self {
        Result::Ok(())
    }

    #[inline]
    fn push_err(&mut self, err: Self::Error) -> ControlFlow {
        *self = Err(err);
        Break
    }

    #[inline]
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection> {
        self.map(|_| val)
    }
}

impl<E> ErrorCollector for Option<E> {
    type Error = E;
    type Collection = E;

    #[inline]
    fn empty() -> Self {
        None
    }

    #[inline]
    fn push_err(&mut self, err: Self::Error) -> ControlFlow {
        *self = Some(err);
        Break
    }

    #[inline]
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection> {
        if let Some(err) = self {
            Err(err)
        } else {
            Ok(val)
        }
    }
}

impl<E> ErrorCollector for Vec<E> {
    type Error = E;
    type Collection = Self;

    #[inline]
    fn empty() -> Self {
        Self::new()
    }

    #[inline]
    fn push_err(&mut self, err: Self::Error) -> ControlFlow {
        self.push(err);
        Continue
    }

    #[inline]
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection> {
        if self.is_empty() {
            Ok(val)
        } else {
            Err(self)
        }
    }
}

#[cfg(feature = "arrayvec")]
use arrayvec::ArrayVec;
use std::convert::Infallible;
use std::marker::PhantomData;

#[cfg(feature = "arrayvec")]
impl<E, const CAP: usize> ErrorCollector for ArrayVec<E, CAP> {
    type Error = E;
    type Collection = Self;

    #[inline]
    fn empty() -> Self {
        Self::new()
    }

    #[inline]
    fn push_err(&mut self, err: Self::Error) -> ControlFlow {
        match self.try_push(err) {
            Ok(_) => Continue,
            Err(_) => Break,
        }
    }

    #[inline]
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection> {
        if self.is_empty() {
            Ok(val)
        } else {
            Err(self)
        }
    }
}
