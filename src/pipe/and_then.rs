//! AndThen combinator
use crate::{Pipe, Result};
use fatal_error::FatalError;
use std::marker::PhantomData;
use tuplify::{FunMut, HList};

/// Combinator that applies a faillible function on the output of a pipe
pub trait AndThenExt<I, O, E, R> {
    /// Applies the given closure on the output of the pipe
    ///
    /// the output of both [`Pipe`] and closure and must be an [`HList`]
    ///
    /// ```rust
    /// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::TagStrError, Incomplete};
    /// # use fatal_error::FatalError;
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
    /// fn yolo(_: &str, _: &str) -> Result<(u8, u8), FatalError<Error>> { Ok((1, 2)) }
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("1").and(tag("2")).and_then(yolo).apply("12"),
    ///     Ok(("", (1u8, 2u8)))
    /// )
    /// ```
    fn and_then<O2, F>(self, f: F) -> AndThen<O, Self, F>
    where
        Self: Sized,
        F: FunMut<O, Output = std::result::Result<O2, FatalError<E>>>,
        O: HList,
        O2: HList,
    {
        AndThen::new(self, f)
    }

    /// Applies the given closure on the output of a pipe
    ///
    /// ```rust
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
    ///     tag::<Error, _, _>("1")
    ///         .and(tag("2"))
    ///         .and_thenf(|(first, second)| Ok(12))
    ///         .apply("12"),
    ///     Ok(("", 12))
    /// )
    /// ```
    fn and_thenf<O2, F>(self, f: F) -> AndThenF<O, Self, F>
    where
        Self: Sized,
        F: FnMut(O) -> std::result::Result<O2, FatalError<E>>,
    {
        AndThenF::new(self, f)
    }

    /// Applies the given closure to the output and remaining input of a pipe
    ///
    /// ```
    /// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::TagStrError, Incomplete, Result, MapExt, OrExt};
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
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum FooBar {
    ///     Foo,
    ///     Bar,
    /// }
    ///
    /// fn true_or_false(input: &str) -> Result<&str, (bool,), Error> {
    ///     tag("true").map1(|_| true).or(tag("false").map1(|_| false)).apply(input)
    /// }
    ///
    /// fn foobar(input: &str) -> Result<&str, (FooBar,), Error> {
    ///     true_or_false
    ///         .ok_and_then(|x, (y,)| {
    ///             if y {
    ///                 tag("bar").map1(|_| FooBar::Bar).apply(x)
    ///             } else {
    ///                 tag("foo").map1(|_| FooBar::Foo).apply(x)
    ///             }
    ///         })
    ///         .apply(input)
    /// }
    ///
    /// assert_eq!(foobar("truebar"), Ok(("", (FooBar::Bar,))));
    /// assert_eq!(foobar("falsefoo"), Ok(("", (FooBar::Foo,))));
    /// assert_eq!(
    ///     tag::<Error, _, _>("1")
    ///         .and(tag("2"))
    ///         .ok_and_then(|r, (first, second)| Ok(("yolo", (12,))))
    ///         .apply("12"),
    ///     Ok(("yolo", (12,)))
    /// )
    /// ```
    fn ok_and_then<O2, R2, F>(self, other: F) -> OkAndThen<O, R, Self, F>
    where
        Self: Sized,
        F: FunMut<(R, O), Output = std::result::Result<(R2, O2), FatalError<E>>>,
    {
        OkAndThen::new(self, other)
    }

    /// Applies the pipes consecutively
    ///
    /// the output of both [`Pipe`] and closure and must be an [`HList`]
    ///
    /// ```rust
    /// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::TagStrError, Incomplete, MapExt, OrExt, Result};
    /// # use fatal_error::FatalError;
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
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum FooBar {
    ///     Foo,
    ///     Bar,
    /// }
    ///
    /// fn true_or_false(input: &str) -> Result<&str, (bool,), Error> {
    ///     tag("true").map1(|_| true).or(tag("false").map1(|_| false)).apply(input)
    /// }
    ///
    /// fn foobar(input: &str) -> Result<&str, (FooBar,), Error> {
    ///     true_or_false
    ///         .ok_then(|(x, (y,))| {
    ///             if y {
    ///                 tag("bar").map1(|_| FooBar::Bar).apply(x)
    ///             } else {
    ///                 tag("foo").map1(|_| FooBar::Foo).apply(x)
    ///             }
    ///         })
    ///         .apply(input)
    /// }
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("1")
    ///         .and(tag("2"))
    ///         .ok_then(|(r, (first, second))| Ok(("yolo", (12,))))
    ///         .apply("12"),
    ///     Ok(("yolo", (12,)))
    /// );
    ///
    /// assert_eq!(foobar("truebar"), Ok(("", (FooBar::Bar,))));
    /// assert_eq!(foobar("falsefoo"), Ok(("", (FooBar::Foo,))));
    /// ```
    #[inline]
    fn ok_then<O2, R2, P>(self, other: P) -> OkThen<O, R, Self, P>
    where
        Self: Pipe<I, O, E, R> + Sized,
        P: Pipe<(R, O), O2, E, R2> + Sized,
    {
        OkThen::new(self, other)
    }
}

impl<I, O, E, R, P> AndThenExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [AndThenExt::and_then] implementation
pub struct AndThen<O, P, F>(P, F, PhantomData<O>);

impl<O, P, F> AndThen<O, P, F> {
    fn new(p: P, f: F) -> Self { AndThen(p, f, PhantomData) }
}

impl<I, O, O2, E, R, P, F> Pipe<I, O2, E, R> for AndThen<O, P, F>
where
    O: HList,
    P: Pipe<I, O, E, R>,
    F: FunMut<O, Output = std::result::Result<O2, FatalError<E>>>,
{
    fn apply(&mut self, input: I) -> Result<R, O2, E> {
        self.0.apply(input).and_then(|(x, y)| Ok((x, self.1.call_fun_mut(y)?)))
    }
}

/// [AndThenExt::and_thenf] implementation
pub struct AndThenF<O, P, F>(P, F, PhantomData<O>);

impl<O, P, F> AndThenF<O, P, F> {
    fn new(p: P, f: F) -> Self { AndThenF(p, f, PhantomData) }
}

impl<I, O, O2, E, R, P, F> Pipe<I, O2, E, R> for AndThenF<O, P, F>
where
    O: HList,
    P: Pipe<I, O, E, R>,
    F: FnMut(O) -> std::result::Result<O2, FatalError<E>>,
{
    fn apply(&mut self, input: I) -> Result<R, O2, E> {
        self.0.apply(input).and_then(|(x, y)| Ok((x, self.1(y)?)))
    }
}

/// [AndThenExt::ok_and_then] implementation
pub struct OkAndThen<O, R, P, P1>(P, P1, PhantomData<O>, PhantomData<R>);

impl<O, R, P, P1> OkAndThen<O, R, P, P1> {
    fn new(p: P, p1: P1) -> Self { Self(p, p1, PhantomData, PhantomData) }
}

impl<I, O, O2, E, R, R2, P, F> Pipe<I, O2, E, R2> for OkAndThen<O, R, P, F>
where
    P: Pipe<I, O, E, R>,
    F: FunMut<(R, O), Output = std::result::Result<(R2, O2), FatalError<E>>>,
{
    fn apply(&mut self, input: I) -> Result<R2, O2, E> {
        self.1.call_fun_mut(self.0.apply(input)?)
    }
}

/// [AndThenExt::ok_then] implementation
pub struct OkThen<O, R, P, P1>(P, P1, PhantomData<O>, PhantomData<R>);

impl<O, R, P, P1> OkThen<O, R, P, P1> {
    fn new(p: P, p1: P1) -> Self { OkThen(p, p1, PhantomData, PhantomData) }
}

impl<I, O, O2, E, R, R2, P, P1> Pipe<I, O2, E, R2> for OkThen<O, R, P, P1>
where
    O: HList,
    P: Pipe<I, O, E, R>,
    P1: Pipe<(R, O), O2, E, R2>,
{
    fn apply(&mut self, input: I) -> Result<R2, O2, E> {
        self.0.apply(input).and_then(|x| self.1.apply(x))
    }
}
