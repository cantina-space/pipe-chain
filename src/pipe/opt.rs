use crate::{Pipe, Result};
use std::marker::PhantomData;
use tuplify::Unpack;

/// Makes a [Pipe] optional
pub trait OptExt<I, O, E> {
    /// Makes a [Pipe] optional if it returns a non fatal error
    ///
    /// example:
    /// ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{tag, Incomplete, str::TagStrError, OptExt, Pipe, Tag};
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
    ///     tag::<Error, _, _>("foo").opt().apply("foobar"),
    ///     Ok(("bar", (Some("foo"),)))
    /// );
    ///
    /// assert_eq!(tag::<Error, _, _>("boo").opt().apply("foobar"), Ok(("foobar", (None,))));
    /// ```
    fn opt(self) -> Opt<Self, O>
    where
        Self: Sized,
        I: Clone,
        O: Unpack,
    {
        Opt::new(self)
    }
}

impl<I, O, E, P> OptExt<I, O, E> for P where P: Pipe<I, O, E> {}

/// [OptExt::opt] implementation
pub struct Opt<P, O> {
    p: P,
    o: PhantomData<O>,
}

impl<P, O> Opt<P, O> {
    fn new(p: P) -> Self { Self { p, o: PhantomData } }
}

impl<I, O, E, P> Pipe<I, (Option<<O as Unpack>::Output>,), E, I> for Opt<P, O>
where
    O: Unpack,
    I: Clone,
    P: Pipe<I, O, E>,
{
    fn apply(&mut self, input: I) -> Result<I, (Option<<O as Unpack>::Output>,), E> {
        self.p.apply(input.clone()).map_or_else(
            |x| x.fatality().map(|_| (input, (None,))),
            |(i, o)| Ok((i, (Some(o.unpack()),))),
        )
    }
}
