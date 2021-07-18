use crate::errors::ErrorCollector;
use crate::{ControlFlow, IterResult};

#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct RawIter<'c, I, C> {
    pub(crate) iter: I,
    pub(crate) errors: &'c mut C,
}

impl<I, C> Iterator for RawIter<'_, I, C>
where
    I: IterResult,
    C: ErrorCollector<Error = I::Error>,
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
