use crate::ControlFlow;
use ControlFlow::*;

pub trait ErrorCollector {
    type Error;
    type Collection;

    fn empty() -> Self;

    fn push_err(&mut self, err: Self::Error) -> ControlFlow;

    fn with_value<T>(self, val: T) -> Result<T, Self::Collection>;
}

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
