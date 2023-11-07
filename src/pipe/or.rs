use crate::{Pipe, Result};
use std::marker::PhantomData;
use tuplify::Unpack;

/// Or combinator
pub trait OrExt<I, O, E, R> {
    /// Apply the second [Pipe] if the first fails
    ///
    /// Example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, OrExt, tag, str::TagStrError, Incomplete};
    /// # use std::error::Error as StdError;
    /// # #[derive(Debug, PartialEq, Eq)]
    /// # enum Error {
    /// #     Incomplete(Incomplete),
    /// #     Tag(TagStrError),
    /// # }
    /// #
    /// # impl std::fmt::Display for Error {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    /// #        write!(f, "{self:?}")
    /// #     }
    /// # }
    /// # impl StdError for Error {}
    /// #
    /// # impl From<Incomplete> for Error {
    /// #     fn from(value: Incomplete) -> Error { Error::Incomplete(value) }
    /// # }
    /// #
    /// # impl From<TagStrError> for Error {
    /// #     fn from(value: TagStrError) -> Error { Error::Tag(value) }
    /// # }
    /// assert_eq!(tag::<Error, _, _>("foo").or(tag("bar")).apply("foo"), Ok(("", ("foo",))));
    ///
    /// assert_eq!(tag::<Error, _, _>("foo").or(tag("boo")).apply("boo"), Ok(("", ("boo",))));
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or(tag("boo")).apply("something"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("boo".into(), "som".into()))))
    /// );
    /// ```
    fn or<P>(self, p: P) -> Or<Self, P>
    where
        Self: Sized,
        I: Clone,
        P: Pipe<I, O, E, R>,
    {
        Or::new(self, p)
    }

    /// Apply the second [Pipe] if the first fails discarding the output of the second pipe
    ///
    /// Example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, OrExt, tag, str::TagStrError, Incomplete};
    /// # use std::error::Error as StdError;
    /// # #[derive(Debug, PartialEq, Eq)]
    /// # enum Error {
    /// #     Incomplete(Incomplete),
    /// #     Tag(TagStrError),
    /// # }
    /// #
    /// # impl std::fmt::Display for Error {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    /// #        write!(f, "{self:?}")
    /// #     }
    /// # }
    /// # impl StdError for Error {}
    /// #
    /// # impl From<Incomplete> for Error {
    /// #     fn from(value: Incomplete) -> Error { Error::Incomplete(value) }
    /// # }
    /// #
    /// # impl From<TagStrError> for Error {
    /// #     fn from(value: TagStrError) -> Error { Error::Tag(value) }
    /// # }
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_self(tag("bar")).apply("foo"),
    ///     Ok(("", (Some("foo"),)))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_self(tag("boo")).apply("boo"),
    ///     Ok(("", (None,)))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_self(tag("boo")).apply("something"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("boo".into(), "som".into()))))
    /// );
    /// ```
    fn or_self<O2, P>(self, p: P) -> OrSelf<O, O2, Self, P>
    where
        Self: Sized,
        O: Unpack,
        I: Clone,
        P: Pipe<I, O2, E, R>,
    {
        OrSelf::new(self, p)
    }

    /// Apply the second [Pipe] if the first fails discarding the output of the first pipe
    ///
    /// Example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, OrExt, tag, str::TagStrError, Incomplete};
    /// # use std::error::Error as StdError;
    /// # #[derive(Debug, PartialEq, Eq)]
    /// # enum Error {
    /// #     Incomplete(Incomplete),
    /// #     Tag(TagStrError),
    /// # }
    /// #
    /// # impl std::fmt::Display for Error {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    /// #        write!(f, "{self:?}")
    /// #     }
    /// # }
    /// # impl StdError for Error {}
    /// #
    /// # impl From<Incomplete> for Error {
    /// #     fn from(value: Incomplete) -> Error { Error::Incomplete(value) }
    /// # }
    /// #
    /// # impl From<TagStrError> for Error {
    /// #     fn from(value: TagStrError) -> Error { Error::Tag(value) }
    /// # }
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_other(tag("bar")).apply("foo"),
    ///     Ok(("", (None,)))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_other(tag("boo")).apply("boo"),
    ///     Ok(("", (Some("boo"),)))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_other(tag("boo")).apply("something"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("boo".into(), "som".into()))))
    /// );
    /// ```
    fn or_other<O2, P>(self, p: P) -> OrOther<O, O2, Self, P>
    where
        Self: Sized,
        I: Clone,
        O2: Unpack,
        P: Pipe<I, O2, E, R>,
    {
        OrOther::new(self, p)
    }
}

impl<I, O, E, R, P> OrExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [OrExt::or] implementation
pub struct Or<P, P1> {
    p:  P,
    p1: P1,
}

impl<P, P1> Or<P, P1> {
    fn new(p: P, p1: P1) -> Self { Self { p, p1 } }
}

impl<I, O, E, R, P, P1> Pipe<I, O, E, R> for Or<P, P1>
where
    P: Pipe<I, O, E, R>,
    P1: Pipe<I, O, E, R>,
    I: Clone,
{
    fn apply(&mut self, input: I) -> Result<R, O, E> {
        match self.p.apply(input.clone()) {
            x @ Ok(_) => x,
            Err(x) => {
                x.fatality()?;
                self.p1.apply(input)
            }
        }
    }
}

/// [OrExt::or_self] implementation
pub struct OrSelf<O, O2, P, P1> {
    p:  P,
    p1: P1,
    o:  PhantomData<O>,
    o2: PhantomData<O2>,
}

impl<O, O2, P, P1> OrSelf<O, O2, P, P1> {
    fn new(p: P, p1: P1) -> Self { Self { p, p1, o: PhantomData, o2: PhantomData } }
}

impl<I, O, O2, E, R, P, P1> Pipe<I, (Option<O::Output>,), E, R> for OrSelf<O, O2, P, P1>
where
    O: Unpack,
    P: Pipe<I, O, E, R>,
    P1: Pipe<I, O2, E, R>,
    I: Clone,
{
    fn apply(&mut self, input: I) -> Result<R, (Option<O::Output>,), E> {
        match self.p.apply(input.clone()).map(|(x, y)| (x, (Some(y.unpack()),))) {
            x @ Ok(_) => x,
            Err(x) => {
                x.fatality()?;
                self.p1.apply(input).map(|(x, _)| (x, (None,)))
            }
        }
    }
}

/// [OrExt::or_other] implementation
pub struct OrOther<O, O2, P, P1> {
    p:  P,
    p1: P1,
    o:  PhantomData<O>,
    o2: PhantomData<O2>,
}

impl<O, O2, P, P1> OrOther<O, O2, P, P1> {
    fn new(p: P, p1: P1) -> Self { Self { p, p1, o: PhantomData, o2: PhantomData } }
}

impl<I, O, O2, E, R, P, P1> Pipe<I, (Option<O2::Output>,), E, R> for OrOther<O, O2, P, P1>
where
    O2: Unpack,
    P: Pipe<I, O, E, R>,
    P1: Pipe<I, O2, E, R>,
    I: Clone,
{
    fn apply(&mut self, input: I) -> Result<R, (Option<O2::Output>,), E> {
        match self.p.apply(input.clone()).map(|(x, _)| (x, (None,))) {
            x @ Ok(_) => x,
            Err(x) => {
                x.fatality()?;
                self.p1.apply(input).map(|(x, y)| (x, (Some(y.unpack()),)))
            }
        }
    }
}

/// [any_of] implementation detail
pub trait AnyOf<I, O, E, R> {
    /// Process the input
    fn apply_any_of(&mut self, input: I) -> Result<R, O, E>;
}

/// Similar to [OrExt::or] but with many possibilities at once
///
/// Example
/// ```
/// # use fatal_error::FatalError;
/// # use pipe_chain::{Pipe, any_of, tag, str::TagStrError, Incomplete};
/// # use std::error::Error as StdError;
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum Error {
/// #     Incomplete(Incomplete),
/// #     Tag(TagStrError),
/// # }
/// #
/// # impl std::fmt::Display for Error {
/// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
/// #        write!(f, "{self:?}")
/// #     }
/// # }
/// # impl StdError for Error {}
/// #
/// # impl From<Incomplete> for Error {
/// #     fn from(value: Incomplete) -> Error { Error::Incomplete(value) }
/// # }
/// #
/// # impl From<TagStrError> for Error {
/// #     fn from(value: TagStrError) -> Error { Error::Tag(value) }
/// # }
/// let mut p = any_of((tag::<Error, _, _>("foo"), tag("bar"), tag("baz")));
///
/// assert_eq!(p.apply("foo"), Ok(("", ("foo",))));
///
/// assert_eq!(p.apply("bar"), Ok(("", ("bar",))));
///
/// assert_eq!(p.apply("baz"), Ok(("", ("baz",))));
///
/// assert_eq!(
///     p.apply("something"),
///     Err(FatalError::Error(Error::Tag(TagStrError("baz".into(), "som".into()))))
/// );
/// ```
pub fn any_of<I, O, E, R>(mut p: impl AnyOf<I, O, E, R>) -> impl Pipe<I, O, E, R> {
    move |x| p.apply_any_of(x)
}

macro_rules! any_of_impl {
    ($_head:ident) => {};
    ($head:ident $($tail:ident) *) => {
        any_of_impl!($($tail) *);

        impl<I: Clone, O, E, R, $head: Pipe<I, O, E, R>, $($tail: Pipe<I, O, E, R>), *> AnyOf<I, O, E, R> for ($head, $($tail), *) {
            #[allow(non_snake_case)]
            fn apply_any_of(&mut self, input: I) -> Result<R, O, E> {
                let ($head, $($tail), *) = self;
                let e = $head.apply(input.clone());
                if e.as_ref().map_or_else(|x|x.is_fatal(), |_| true) { return e; }
                $(
                    let e = $tail.apply(input.clone());
                    if e.as_ref().map_or_else(|x|x.is_fatal(), |_| true) { return e; }
                ) *
                e
            }
        }
    };
}

any_of_impl!(T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32);
