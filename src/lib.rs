use crate::errors::Ignore;
use crate::raw_iter::RawIter;
use errors::ErrorCollector;

pub mod errors;
mod raw_iter;

pub trait IterResult: Iterator<Item = Result<Self::Ok, Self::Error>> + Sized {
    type Ok;
    type Error;

    #[inline]
    fn failfast(self) -> Fallible<Self, Option<Self::Error>> {
        self.fallible()
    }

    #[inline]
    fn ignore(self) -> Fallible<Self, Ignore<Self::Error>> {
        self.fallible()
    }

    #[inline]
    fn accumulate(self) -> Fallible<Self, Vec<Self::Error>> {
        self.fallible()
    }

    #[inline]
    fn fallible<C: ErrorCollector<Error = Self::Error>>(self) -> Fallible<Self, C> {
        self.with_collector(C::empty())
    }

    #[inline]
    fn with_collector<C: ErrorCollector<Error = Self::Error>>(
        self,
        collector: C,
    ) -> Fallible<Self, C> {
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

impl<I, C> Fallible<I, C>
where
    I: IterResult,
    C: ErrorCollector<Error = I::Error>,
{
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

#[derive(Debug, Copy, Clone)]
pub enum ControlFlow {
    Break,
    Continue,
}

#[macro_export]
macro_rules! fallible {
    ($base:expr) => {
        $base
    };
    ($base:expr, $($b_type:ty :)? | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        crate::Fallible::process$(::<_, $b_type>)?($base, |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
    ($base:expr, $($b_type:ty :)? move | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        crate::Fallible::process$(::<_, $b_type>)?($base, move |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
    ($base:expr, no_discard $($b_type:ty :)? | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        crate::Fallible::process_no_discard$(::<_, $b_type>)?($base, |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
    ($base:expr, no_discard $($b_type:ty :)? move | $id:ident $(: $ty:ty)? | $expr:expr $(, $($tail:tt)+)? ) => {
        crate::Fallible::process_no_discard$(::<_, $b_type>)?($base, move |$id $(: $ty:ty)?| fallible!($expr $(, $($tail)+)?))
    };
}

#[cfg(test)]
mod tests {
    use crate::errors::Ignore;
    use crate::IterResult;
    use std::fs::File;
    use std::io::{BufRead, BufReader};
    use std::path::Path;

    #[test]
    fn test_fail_fast() {
        let v = vec![Ok(1i64), Ok(4), Ok(-3), Err("Error"), Ok(10)];
        let res: Result<i64, _> = v.into_iter().failfast().process(|it| it.sum());
        assert_eq!(res, Err("Error"));
    }

    #[test]
    fn test_success() {
        let v: Vec<Result<_, &str>> = vec![Ok(1i64), Ok(4), Ok(-3), Ok(10)];
        let res: i64 = v.into_iter().failfast().process(|it| it.sum()).unwrap();
        assert_eq!(res, 12);
    }

    #[test]
    fn test_filter() {
        let v = vec![Ok(1i64), Ok(4), Ok(-3), Err("Error"), Ok(10)];
        let res: i64 = v
            .into_iter()
            .with_collector(Ignore::default())
            .process(|it| it.sum())
            .unwrap();
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
                .map(|entry| File::open(entry.path())).failfast(),
            |it| it.map(BufReader::new).flat_map(|f| f.lines()).failfast(),
            |it| it.map(|ln| ln.parse::<i32>()).accumulate(),
            no_discard i32: |it| it.sum()
        )???;
        assert_eq!(sum, 11966);
        assert_eq!(
            err,
            Some(
                vec![
                    "sadfs",
                    "1000000000000000000000000000000000000000000000000000000000",
                    "hello world",
                    "1.35"
                ]
                .into_iter()
                .map(str::parse::<i32>)
                .map(Result::unwrap_err)
                .collect()
            )
        );
        Ok(())
    }
}
