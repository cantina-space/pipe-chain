use crate::{Pipe, Result};

/// Wrap a [Pipe] into a [Box]
pub trait BoxedExt<I, O, E, R = I> {
    /// Wraps the current [`Pipe`] into a [`Box`]
    ///
    /// example:
    /// ```
    /// # use pipe_chain::{Pipe, BoxedPipe, BoxedExt, AndExt, tag, str::TagStrError, Incomplete};
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
    /// fn mk_pipe<'a>() -> BoxedPipe<'a, &'a str, (&'a str, &'a str), Error> {
    ///     tag::<Error, _, _>("1").and(tag("2")).boxed()
    /// }
    ///
    /// fn mk_pipe2<'a>() -> BoxedPipe<'a, &'a str, (&'a str, &'a str), Error> {
    ///     tag::<Error, _, _>("1").and(tag("2")).and_self(tag("3")).boxed()
    /// }
    ///
    /// let mut v = vec![mk_pipe(), mk_pipe2()];
    ///
    /// assert_eq!(v[0].apply("123"), Ok(("3", ("1", "2"))));
    /// assert_eq!(v[1].apply("123"), Ok(("", ("1", "2"))));
    /// ```
    fn boxed<'a>(self) -> BoxedPipe<'a, I, O, E, R>
    where
        Self: Pipe<I, O, E, R> + Sized + 'a,
    {
        BoxedPipe::new(self)
    }
}

impl<I, O, E, R, P> BoxedExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [BoxedExt::boxed] implementation
pub struct BoxedPipe<'a, I, O, E, R = I>(Box<dyn Pipe<I, O, E, R> + 'a>);

impl<'a, I, O, E, R> BoxedPipe<'a, I, O, E, R> {
    fn new<P>(p: P) -> Self
    where
        P: Pipe<I, O, E, R> + Sized + 'a,
    {
        Self(Box::new(p))
    }
}

impl<'a, I, O, E, R> Pipe<I, O, E, R> for BoxedPipe<'a, I, O, E, R> {
    fn apply(&mut self, input: I) -> Result<R, O, E> { self.0.apply(input) }
}
