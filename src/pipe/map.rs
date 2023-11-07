use crate::{Pipe, Result};
use fatal_error::FatalError;
use std::marker::PhantomData;
use tuplify::{FunMut, HList};

/// Combinator that transforms a part of a pipe
pub trait MapExt<I, O, E, R> {
    /// Maps the output of a pipe `O` to `O2` by applying a function to it.
    ///
    /// Example:
    /// ```
    /// # use pipe_chain::{tag, str::TagStrError, MapExt, Pipe, Incomplete};
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
    /// assert_eq!(
    ///     tag::<Error, _, _>("a").map(|_| (1, 2, 3)).apply("a"),
    ///     Ok(("", (1, 2, 3)))
    /// );
    /// ```
    fn map<F>(self, f: F) -> Map<Self, F, O>
    where
        Self: Sized,
        O: HList,
        F: FunMut<O>,
    {
        Map::new(self, f)
    }
    /// Maps the output of a pipe `O` to `O2` by applying a function to it.
    /// The result is mapped into a tuple
    /// ```
    /// # use pipe_chain::{tag, str::TagStrError, MapExt, Pipe, Incomplete};
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
    /// assert_eq!(
    ///     tag::<Error, _, _>("a").map1(|_| (1, 2, 3)).apply("a"),
    ///     Ok(("", ((1, 2, 3),)))
    /// );
    /// assert_eq!(tag::<Error, _, _>("a").map1(|_| 1).apply("a"), Ok(("", (1,))));
    /// ```
    fn map1<F>(self, f: F) -> Map1<Self, F, O>
    where
        Self: Sized,
        O: HList,
        F: FunMut<O>,
    {
        Map1::new(self, f)
    }

    /// Maps the output of a pipe `O` to `O2` by applying a function to it.
    /// The result is mapped into a tuple
    /// ```
    /// # use pipe_chain::{tag, str::TagStrError, MapExt, Pipe, Incomplete};
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
    /// assert_eq!(tag::<Error, _, _>("a").mapf(|_| 1).apply("a"), Ok(("", 1)));
    /// assert_eq!(tag::<Error, _, _>("a").mapf(|(x,)| x).apply("a"), Ok(("", "a")));
    /// ```
    fn mapf<O2, F>(self, f: F) -> MapF<Self, F, O>
    where
        Self: Sized,
        F: FnMut(O) -> O2,
    {
        MapF::new(self, f)
    }

    /// Maps an error `FatalError<E>` to `FatalError<E2>` by applying a function to the error.
    ///
    /// ```
    /// # use pipe_chain::{tag, str::{digits, TagStrError}, MapExt, Pipe, Incomplete, EitherExt};
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
    /// #[derive(Debug, PartialEq)]
    /// struct MyError;
    ///
    /// assert_eq!(tag::<Error, _, _>("a").map_err(|_| FatalError::Error(MyError)).apply("b"),
    ///            Err(FatalError::Error(MyError))
    /// );
    /// ```
    fn map_err<E2, F>(self, f: F) -> MapErr<Self, F, E>
    where
        Self: Sized,
        F: FnMut(FatalError<E>) -> FatalError<E2>,
    {
        MapErr::new(self, f)
    }
}

impl<I, O, E, R, P> MapExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [MapExt::map] implementation
pub struct Map<P, F, O> {
    p: P,
    f: F,
    o: PhantomData<O>,
}

impl<P, F, O> Map<P, F, O> {
    fn new(p: P, f: F) -> Self { Self { p, f, o: PhantomData } }
}

impl<I, O, O2, E, R, F, P> Pipe<I, O2, E, R> for Map<P, F, O>
where
    O: HList,
    F: FunMut<O, Output = O2>,
    P: Pipe<I, O, E, R>,
{
    fn apply(&mut self, input: I) -> Result<R, O2, E> {
        self.p.apply(input).map(|(i, o)| (i, self.f.call_fun_mut(o)))
    }
}

/// [MapExt::map1] implementation
pub struct Map1<P, F, O> {
    p: P,
    f: F,
    o: PhantomData<O>,
}

impl<P, F, O> Map1<P, F, O> {
    fn new(p: P, f: F) -> Self { Self { p, f, o: PhantomData } }
}

impl<I, O, O2, E, R, F, P> Pipe<I, (O2,), E, R> for Map1<P, F, O>
where
    F: FunMut<O, Output = O2>,
    P: Pipe<I, O, E, R>,
    O: HList,
{
    fn apply(&mut self, input: I) -> Result<R, (O2,), E> {
        self.p.apply(input).map(|(i, o)| (i, (self.f.call_fun_mut(o),)))
    }
}

/// [MapExt::mapf] implementation
pub struct MapF<P, F, O> {
    p: P,
    f: F,
    o: PhantomData<O>,
}

impl<P, F, O> MapF<P, F, O> {
    fn new(p: P, f: F) -> Self { Self { p, f, o: PhantomData } }
}

impl<I, O, O2, E, R, F, P> Pipe<I, O2, E, R> for MapF<P, F, O>
where
    F: FnMut(O) -> O2,
    P: Pipe<I, O, E, R>,
{
    fn apply(&mut self, input: I) -> Result<R, O2, E> {
        self.p.apply(input).map(|(i, o)| (i, (self.f)(o)))
    }
}

/// [MapExt::map_err] implementation
pub struct MapErr<P, F, E> {
    p: P,
    f: F,
    e: PhantomData<E>,
}

impl<P, F, E> MapErr<P, F, E> {
    fn new(p: P, f: F) -> Self { Self { p, f, e: PhantomData } }
}

impl<I, O, E, E2, R, P, F> Pipe<I, O, E2, R> for MapErr<P, F, E>
where
    P: Pipe<I, O, E, R>,
    F: FnMut(FatalError<E>) -> FatalError<E2>,
{
    fn apply(&mut self, input: I) -> Result<R, O, E2> {
        self.p.apply(input).map_err(|x| (self.f)(x))
    }
}
