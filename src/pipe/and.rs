//! And combinator
use crate::{Pipe, Result};
use std::marker::PhantomData;
use tuplify::{Extend, HList};

/// Combinator that chains 2 pipes together
pub trait AndExt<I, O, E, R> {
    /// Chains 2 [`Pipe`]s one after another
    ///
    /// The 2 output are combined into a single [`HList`]
    ///
    /// Example:
    /// ```rust
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::TagStrError, Incomplete};
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
    ///     tag::<Error, _, _>("foo").and(tag("bar")).apply("foobar"),
    ///     Ok(("", ("foo", "bar")))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").and(tag("boo")).apply("foobar"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("boo".into(), "bar".into()))))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").and(tag("boo")).apply("foobo"),
    ///     Err(FatalError::Error(Error::Incomplete(Incomplete::Size(1))))
    /// );
    /// ```
    fn and<O2, R2, P>(self, p: P) -> And<Self, P, O, O2, R>
    where
        Self: Sized,
        O: Extend<O2>,
        O2: HList,
        P: Pipe<R, O2, E, R2>,
    {
        And::new(self, p)
    }

    /// Chains 2 [`Pipe`]s one after another
    ///
    /// Only the output of the second pipe is returned
    ///
    /// Example:
    /// ```rust
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::TagStrError, Incomplete};
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
    ///     tag::<Error, _, _>("foo").and_other(tag("bar")).apply("foobar"),
    ///     Ok(("", ("bar",)))
    /// );
    /// ```
    fn and_other<O2, R2, P>(self, p: P) -> AndOther<Self, P, O, R>
    where
        Self: Sized,
        P: Pipe<R, O2, E, R2>,
    {
        AndOther::new(self, p)
    }

    /// Chains 2 [`Pipe`]s one after another
    ///
    /// Only the output of the first pipe is returned
    ///
    /// Example:
    /// ```rust
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::TagStrError, Incomplete};
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
    ///     tag::<Error, _, _>("foo").and_self(tag("bar")).apply("foobar"),
    ///     Ok(("", ("foo",)))
    /// );
    /// ```
    fn and_self<O2, R2, P>(self, other: P) -> AndSelf<Self, P, R, O2>
    where
        Self: Sized,
        P: Pipe<R, O2, E, R2>,
    {
        AndSelf::new(self, other)
    }
}

impl<I, O, E, R, P> AndExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [AndExt::and] implementation
pub struct And<P, P1, O, O2, R> {
    p:   P,
    p1:  P1,
    _o:  PhantomData<O>,
    _o2: PhantomData<O2>,
    _r:  PhantomData<R>,
}

impl<P, P1, O, O2, R> And<P, P1, O, O2, R> {
    fn new(p: P, p1: P1) -> Self {
        Self { p, p1, _o: PhantomData, _o2: PhantomData, _r: PhantomData }
    }
}

impl<I, O, O2, E, R, R2, P, P1> Pipe<I, O::Output, E, R2> for And<P, P1, O, O2, R>
where
    O: Extend<O2>,
    O2: HList,
    P: Pipe<I, O, E, R>,
    P1: Pipe<R, O2, E, R2>,
{
    fn apply(&mut self, input: I) -> Result<R2, O::Output, E> {
        let (i, o) = self.p.apply(input)?;
        self.p1.apply(i).map(|(i, o2)| (i, o.extend(o2)))
    }
}

/// [AndExt::and_other] implementation
pub struct AndOther<P1, P2, O, R>(P1, P2, PhantomData<O>, PhantomData<R>);

impl<P1, P2, O, R> AndOther<P1, P2, O, R> {
    fn new(p: P1, p1: P2) -> AndOther<P1, P2, O, R> {
        AndOther(p, p1, PhantomData, PhantomData)
    }
}

impl<I, O, E, R, O2, R2, P1, P2> Pipe<I, O2, E, R2> for AndOther<P1, P2, O, R>
where
    P1: Pipe<I, O, E, R>,
    P2: Pipe<R, O2, E, R2>,
{
    fn apply(&mut self, input: I) -> Result<R2, O2, E> {
        self.0.apply(input).and_then(|(i, _)| self.1.apply(i).map(|(i, o)| (i, o)))
    }
}

/// [AndExt::and_self] implementation
pub struct AndSelf<P1, P2, R, O2>(P1, P2, PhantomData<R>, PhantomData<O2>);

impl<P1, P2, R, O2> AndSelf<P1, P2, R, O2> {
    fn new(p: P1, p1: P2) -> AndSelf<P1, P2, R, O2> {
        AndSelf(p, p1, PhantomData, PhantomData)
    }
}

impl<I, O, E, R, O2, R2, P1, P2> Pipe<I, O, E, R2> for AndSelf<P1, P2, R, O2>
where
    P1: Pipe<I, O, E, R>,
    P2: Pipe<R, O2, E, R2>,
{
    fn apply(&mut self, input: I) -> Result<R2, O, E> {
        self.0.apply(input).and_then(|(i, o)| self.1.apply(i).map(|(i, _)| (i, o)))
    }
}
