use crate::{Pipe, Result};
use std::marker::PhantomData;

/// Combinator that discards output
pub trait SkipExt<I, O, E, R> {
    /// Discards the output of the pipe
    ///
    /// Example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, SkipExt, tag, str::TagStrError, Incomplete};
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
    /// assert_eq!(tag::<Error, _, _>("foo").skip().apply("foobar"), Ok(("bar", ())));
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").skip().apply("something"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("foo".into(), "som".into()))))
    /// );
    /// ```
    fn skip(self) -> Skip<Self, O>
    where
        Self: Sized,
    {
        Skip::new(self)
    }

    /// Chains 2 [`Pipe`]s one after another both output are discarded
    ///
    /// Example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, SkipExt, tag, str::TagStrError, Incomplete};
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
    ///     tag::<Error, _, _>("foo").and_skip(tag("bar")).apply("foobar"),
    ///     Ok(("", ()))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").and_skip(tag("boo")).apply("something"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("foo".into(), "som".into()))))
    /// );
    /// ```
    fn and_skip<O2, R2, P>(self, other: P) -> AndSkip<Self, P, O, O2, R>
    where
        Self: Sized,
        P: Pipe<R, O2, E, R2>,
    {
        AndSkip::new(self, other)
    }

    /// Apply the second [Pipe] if the first fails discarding both output
    ///
    /// Example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, SkipExt, tag, str::TagStrError, Incomplete};
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
    /// assert_eq!(tag::<Error, _, _>("foo").or_skip(tag("bar")).apply("foo"), Ok(("", ())));
    ///
    /// assert_eq!(tag::<Error, _, _>("foo").or_skip(tag("boo")).apply("boo"), Ok(("", ())));
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").or_skip(tag("boo")).apply("something"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("boo".into(), "som".into()))))
    /// );
    /// ```
    fn or_skip<O2, P>(self, p: P) -> OrSkip<O, O2, Self, P>
    where
        Self: Sized,
        I: Clone,
        P: Pipe<I, O2, E, R>,
    {
        OrSkip::new(self, p)
    }
}

impl<I, O, E, R, P> SkipExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [SkipExt::skip] implementation
pub struct Skip<P, O> {
    p: P,
    o: PhantomData<O>,
}

impl<P, O> Skip<P, O> {
    fn new(p: P) -> Self { Self { p, o: PhantomData } }
}

impl<I, I2, O, E, P> Pipe<I, (), E, I2> for Skip<P, O>
where
    P: Pipe<I, O, E, I2>,
{
    fn apply(&mut self, input: I) -> Result<I2, (), E> {
        self.p.apply(input).map(|x| (x.0, ()))
    }
}

/// [SkipExt::and_skip] implementation
pub struct AndSkip<P1, P2, O, O2, R>(
    P1,
    P2,
    PhantomData<O>,
    PhantomData<O2>,
    PhantomData<R>,
);

impl<P1, P2, O, O2, R> AndSkip<P1, P2, O, O2, R> {
    fn new(p: P1, p1: P2) -> AndSkip<P1, P2, O, O2, R> {
        AndSkip(p, p1, PhantomData, PhantomData, PhantomData)
    }
}

impl<I, O, E, R, O2, R2, P1, P2> Pipe<I, (), E, R2> for AndSkip<P1, P2, O, O2, R>
where
    P1: Pipe<I, O, E, R>,
    P2: Pipe<R, O2, E, R2>,
{
    fn apply(&mut self, input: I) -> Result<R2, (), E> {
        self.0.apply(input).and_then(|(i, _)| self.1.apply(i).map(|(i, _)| (i, ())))
    }
}

/// [SkipExt::or_skip] implementation
pub struct OrSkip<O, O2, P, P1> {
    p:  P,
    p1: P1,
    o:  PhantomData<O>,
    o2: PhantomData<O2>,
}

impl<O, O2, P, P1> OrSkip<O, O2, P, P1> {
    fn new(p: P, p1: P1) -> Self { Self { p, p1, o: PhantomData, o2: PhantomData } }
}

impl<I, O, O2, E, R, P, P1> Pipe<I, (), E, R> for OrSkip<O, O2, P, P1>
where
    P: Pipe<I, O, E, R>,
    P1: Pipe<I, O2, E, R>,
    I: Clone,
{
    fn apply(&mut self, input: I) -> Result<R, (), E> {
        match self.p.apply(input.clone()).map(|(x, _)| (x, ())) {
            x @ Ok(_) => x,
            Err(x) => {
                x.fatality()?;
                self.p1.apply(input).map(|(x, _)| (x, ()))
            }
        }
    }
}
