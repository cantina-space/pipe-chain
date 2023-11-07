//! Either combinator
use crate::{Pipe, Result};
use either::Either;
use std::marker::PhantomData;
use tuplify::Unpack;

/// Either combinator
///
/// Combine 2 [`Pipe`]s that can produce different outputs but share the same input
pub trait EitherExt<I, O, E, R> {
    /// Combine 2 [Pipe]s with the same input and remaining but differents outputs
    ///
    /// ```
    /// # use pipe_chain::{str::digits, tag, EitherExt, str::TagStrError, Incomplete, MapExt, Pipe};
    /// # use either::Either;
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
    /// let mut p =
    ///     tag::<Error, _, _>("a").either(digits::<Error>(1..).map1(|x: &str| x.parse().unwrap()));
    ///
    /// assert_eq!(p.apply("a"), Ok(("", (Either::Left("a"),))));
    /// assert_eq!(p.apply("12"), Ok(("", (Either::Right(12u32),))));
    /// ```
    fn either<O2, P>(self, p: P) -> EitherPipe<O, O2, Self, P>
    where
        I: Clone,
        Self: Pipe<I, O, E, R> + Sized,
        P: Pipe<I, O2, E, R>,
    {
        EitherPipe::new(self, p)
    }

    /// Combine 2 [Pipe]s with the same input and differents outputs and remaining
    ///
    /// ```
    /// #  use pipe_chain::{
    ///     str::digits, tag, AndThenExt, EitherExt, str::TagStrError, Incomplete, MapExt, Pipe,
    /// };
    /// # use either::Either;
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
    /// let mut p = tag::<Error, _, _>("a").either_full(
    ///     digits::<Error>(1..).map1(|x: &str| x.parse().unwrap()).ok_and_then(|_, x| Ok((0, x))),
    /// );
    ///
    /// assert_eq!(p.apply("a"), Ok((Either::Left(""), (Either::Left("a"),))));
    /// assert_eq!(p.apply("12"), Ok((Either::Right(0), (Either::Right(12u32),))));
    /// ```
    fn either_full<O2, R2, P>(self, p: P) -> EitherPipeFull<O, O2, Self, P>
    where
        I: Clone,
        Self: Pipe<I, O, E, R> + Sized,
        P: Pipe<I, O2, E, R2>,
    {
        EitherPipeFull::new(self, p)
    }
}

impl<I, O, E, R, P> EitherExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [EitherExt::either] implementation
pub struct EitherPipe<O, O2, P, P1>(P, P1, PhantomData<O>, PhantomData<O2>);

impl<O, O2, P, P1> EitherPipe<O, O2, P, P1> {
    fn new(p: P, p1: P1) -> Self { Self(p, p1, PhantomData, PhantomData) }
}

impl<I, O, O2, E, R, P, P1> Pipe<I, (Either<O::Output, O2::Output>,), E, R>
    for EitherPipe<O, O2, P, P1>
where
    I: Clone,
    O: Unpack,
    O2: Unpack,
    P: Pipe<I, O, E, R> + Sized,
    P1: Pipe<I, O2, E, R>,
{
    fn apply(&mut self, input: I) -> Result<R, (Either<O::Output, O2::Output>,), E> {
        self.0
            .apply(input.clone())
            .map(|(i, o)| (i, (Either::Left(o.unpack()),)))
            .or_else(|x| {
                x.fatality()?;
                self.1.apply(input).map(|(i, x)| (i, (Either::Right(x.unpack()),)))
            })
    }
}

/// [EitherExt::either_full] implementation
pub struct EitherPipeFull<O, O2, P, P1>(P, P1, PhantomData<O>, PhantomData<O2>);

impl<O, O2, P, P1> EitherPipeFull<O, O2, P, P1> {
    fn new(p: P, p1: P1) -> Self { Self(p, p1, PhantomData, PhantomData) }
}

impl<I, O, O2, E, R, R2, P, P1>
    Pipe<I, (Either<O::Output, O2::Output>,), E, Either<R, R2>>
    for EitherPipeFull<O, O2, P, P1>
where
    I: Clone,
    O: Unpack,
    O2: Unpack,
    P: Pipe<I, O, E, R> + Sized,
    P1: Pipe<I, O2, E, R2>,
{
    fn apply(
        &mut self, input: I,
    ) -> Result<Either<R, R2>, (Either<O::Output, O2::Output>,), E> {
        self.0
            .apply(input.clone())
            .map(|(i, o)| (Either::Left(i), (Either::Left(o.unpack()),)))
            .or_else(|x| {
                x.fatality()?;
                self.1
                    .apply(input)
                    .map(|(i, x)| (Either::Right(i), (Either::Right(x.unpack()),)))
            })
    }
}
