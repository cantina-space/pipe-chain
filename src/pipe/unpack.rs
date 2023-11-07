use crate::{Pipe, Result};
use std::marker::PhantomData;
use tuplify::Unpack;

/// Combinator that calls [tuplify::Unpack::unpack] on it's output
pub trait UnpackExt<I, O, E, R> {
    /// Unpacks the output of a pipe
    ///
    /// Example:
    /// ```rust
    /// # use fatal_error::FatalError;
    /// # use pipe_chain::{Pipe, AndExt, UnpackExt, tag, Incomplete, str::TagStrError};
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
    /// # impl From<Incomplete> for Error {
    /// #     fn from(value: Incomplete) -> Error { Error::Incomplete(value) }
    /// # }
    /// #
    /// # impl From<TagStrError> for Error {
    /// #     fn from(value: TagStrError) -> Error { Error::Tag(value) }
    /// # }
    /// // unpacking many elements does nothing
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").and(tag("bar")).unpack().apply("foobar"),
    ///     Ok(("", ("foo", "bar")))
    /// );
    ///
    /// // single element without unpacking
    /// assert_eq!(tag::<Error, _, _>("foo").apply("foo"), Ok(("", ("foo",))));
    ///
    /// // single element with unpacking
    /// assert_eq!(tag::<Error, _, _>("foo").unpack().apply("foo"), Ok(("", "foo")));
    /// ```
    fn unpack(self) -> UnpackPipe<Self, O>
    where
        O: Unpack,
        Self: Sized,
    {
        UnpackPipe::new(self)
    }
}

impl<I, O, E, R, P> UnpackExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [UnpackExt::unpack] implementation
pub struct UnpackPipe<P, O> {
    p: P,
    o: PhantomData<O>,
}

impl<P, O> UnpackPipe<P, O> {
    fn new(p: P) -> Self { Self { p, o: PhantomData } }
}

impl<I, O, E, R, P> Pipe<I, O::Output, E, R> for UnpackPipe<P, O>
where
    O: Unpack,
    P: Pipe<I, O, E, R>,
{
    fn apply(&mut self, input: I) -> Result<R, O::Output, E> {
        self.p.apply(input).map(|(i, o)| (i, o.unpack()))
    }
}
