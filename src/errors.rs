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
pub trait ErrorCollector<E> {
    /// The type to be returned after the iteration has been stopped
    type Collection;

    /// Creates an empty `ErrorCollector`.
    fn empty() -> Self;

    /// Processes an error. Returns an [`ControlFlow`] type indicating whether the iteration shall stop
    /// or not.
    fn push_err(&mut self, err: E) -> ControlFlow;

    /// Returns `Ok(val)` if the iteration run to completion, or an error collection of type
    /// [`Self::Collection`][ErrorCollector::Collection] if error(s) were encountered.
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection>;
}

/// A unit type that implements [`ErrorCollector`]. Ignores all errors and runs the iterator to
/// completion
#[derive(Debug, Copy, Clone)]
pub struct Ignore;

impl<E> ErrorCollector<E> for Ignore {
    type Collection = Infallible;

    #[inline]
    fn empty() -> Self {
        Self
    }

    #[inline]
    fn push_err(&mut self, _err: E) -> ControlFlow {
        Continue
    }

    #[inline]
    fn with_value<T>(self, val: T) -> Result<T, Self::Collection> {
        Ok(val)
    }
}

impl<E, F: From<E>> ErrorCollector<E> for Option<F> {
    type Collection = F;

    #[inline]
    fn empty() -> Self {
        None
    }

    #[inline]
    fn push_err(&mut self, err: E) -> ControlFlow {
        *self = Some(err.into());
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

impl<E, F: From<E>> ErrorCollector<E> for Vec<F> {
    type Collection = Self;

    #[inline]
    fn empty() -> Self {
        Self::new()
    }

    #[inline]
    fn push_err(&mut self, err: E) -> ControlFlow {
        self.push(err.into());
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

/// Store upto N errors in an `ArrayVec<E, N>`. Stop the iteration if more are encountered.
#[cfg(feature = "arrayvec")]
impl<E, F: From<E>, const CAP: usize> ErrorCollector<E> for ArrayVec<F, CAP> {
    type Collection = Self;

    #[inline]
    fn empty() -> Self {
        Self::new()
    }

    #[inline]
    fn push_err(&mut self, err: E) -> ControlFlow {
        match self.try_push(err.into()) {
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
