use crate::errors::{ControlFlow, ErrorCollector};
use crate::IterResult;

/// An iterator adaptor wrapping an iterator with [`Result<T, E>`] elements and implements
/// `Iterator<Item=T>`. Used only in [`Fallible::process`][`crate::Fallible::process`] and
/// [`Fallible::process_no_discard`][crate::Fallible::process_no_discard].
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct RawIter<'c, I, C> {
    pub(crate) iter: I,
    pub(crate) errors: &'c mut C,
}

impl<I, C> Iterator for RawIter<'_, I, C>
where
    I: IterResult,
    C: ErrorCollector<I::Error>,
{
    type Item = I::Ok;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                Some(Ok(item)) => {
                    break item.into();
                }
                Some(Err(err)) => {
                    if let ControlFlow::Break = self.errors.push_err(err) {
                        break None;
                    }
                }
                None => {
                    break None;
                }
            }
        }
    }

    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut f = f; // to appease the IntelliJ Rust
        let Self { mut iter, errors } = self;
        let res = iter.try_fold(init, |acc, item| match item {
            Ok(ok) => Ok(f(acc, ok)),
            Err(err) => {
                if let ControlFlow::Break = errors.push_err(err) {
                    Err(acc)
                } else {
                    Ok(acc)
                }
            }
        });
        match res {
            Ok(inner) => inner,
            Err(inner) => inner,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::raw_iter::RawIter;
    use arrayvec::ArrayVec;
    use std::ops::Add;

    #[test]
    fn test() {
        let v = vec![
            Ok(1i64),
            Err("Error1"),
            Ok(4),
            Err("Error2"),
            Ok(-3),
            Err("Error3"),
            Ok(10),
        ];
        let mut col = ArrayVec::<&str, 2>::new();
        let iter = RawIter {
            iter: v.into_iter(),
            errors: &mut col,
        };
        assert_eq!(iter.collect::<Vec<_>>(), vec![1, 4, -3]);
        assert_eq!(col.into_inner().unwrap(), ["Error1", "Error2"]);
    }

    #[test]
    fn test_fold() {
        let v = vec![
            Ok(1i64),
            Err("Error1"),
            Ok(4),
            Err("Error2"),
            Ok(-3),
            Err("Error3"),
            Ok(10),
        ];
        let mut col = ArrayVec::<&str, 2>::new();
        let iter = RawIter {
            iter: v.into_iter(),
            errors: &mut col,
        };
        assert_eq!(iter.fold(0, i64::add), 2);
        assert_eq!(col.into_inner().unwrap(), ["Error1", "Error2"]);
    }
}
