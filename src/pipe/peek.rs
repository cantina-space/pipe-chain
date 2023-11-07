use crate::{Pipe, Result};
use std::marker::PhantomData;

/// Applies a [Pipe] without consuming the input
pub trait PeekExt<I, O, E, R> {
    /// Makes a [Pipe] optional if it returns a non fatal error
    ///
    /// example:
    ///  ```
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, PeekExt, tag, str::TagStrError, Incomplete};
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
    ///     tag::<Error, _, _>("foo").peek().apply("foobar"),
    ///     Ok(("foobar", ("foo",)))
    /// );
    ///
    /// assert_eq!(
    ///     tag::<Error, _, _>("boo").peek().apply("foobar"),
    ///     Err(FatalError::Error(Error::Tag(TagStrError("boo".into(), "foo".into()))))
    /// );
    /// ```
    fn peek(self) -> Peek<Self, R>
    where
        Self: Sized,
        I: Clone,
    {
        Peek::new(self)
    }
}

impl<I: Clone, O, E, R, P: Pipe<I, O, E, R>> PeekExt<I, O, E, R> for P {}

/// [PeekExt::peek] implementation
pub struct Peek<P, R>(P, PhantomData<R>);

impl<P, R> Peek<P, R> {
    fn new(p: P) -> Self { Peek(p, PhantomData) }
}

impl<I, O, E, R, P> Pipe<I, O, E> for Peek<P, R>
where
    I: Clone,
    P: Pipe<I, O, E, R>,
{
    fn apply(&mut self, input: I) -> Result<I, O, E> {
        self.0.apply(input.clone()).map(|(_, x)| (input, x))
    }
}
