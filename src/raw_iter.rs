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
}
