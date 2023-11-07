use crate::{Pipe, Result};
use std::marker::PhantomData;
/// Wraps the pipe and input/ouput into a closure
pub trait WrapExt<I, O, E, R> {
    /// wraps self into a function
    /// ```rust
    /// # use pipe_chain::{str::TagStrError, tag, AndExt, Incomplete, Pipe, WrapExt, Result};
    /// # use std::error::Error as StdError;
    /// # #[derive(Debug, PartialEq, Eq)]
    /// # enum Error {
    /// #     Tag(TagStrError),
    /// #     Incomplete(Incomplete),
    /// # }
    /// #
    /// # impl std::fmt::Display for Error {
    /// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    /// #         write!(f, "{self:?}")
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
    /// #
    /// pub fn input_offset<'a, O, E>(
    ///     p: &mut impl Pipe<&'a str, O, E>, input: (&'a str, usize),
    /// ) -> Result<(&'a str, usize), O, E> {
    ///     let (i, o) = p.apply(input.0)?;
    ///     Ok(((i, input.1 + (input.0.len() - i.len())), o))
    /// }
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").and(tag("bar")).wrap(input_offset).apply(("foobar", 0)),
    ///     Ok((("", 6), ("foo", "bar")))
    /// );
    /// assert_eq!(
    ///     tag::<Error, _, _>("foo").and(tag("bar")).wrap(input_offset).apply(("foobar", 0)),
    ///     Ok((("", 6), ("foo", "bar")))
    /// );
    /// ```
    fn wrap<I2, O2, R2, F>(self, f: F) -> Wrap<I, O, R, Self, F>
    where
        Self: Pipe<I, O, E, R> + Sized,
        F: FnMut(&mut Self, I2) -> Result<R2, O2, E>,
    {
        Wrap::new(self, f)
    }
}

impl<I, O, E, R, P: Pipe<I, O, E, R>> WrapExt<I, O, E, R> for P {}

/// [WrapExt::wrap] implementation
pub struct Wrap<I, O, R, P, F>(P, F, PhantomData<I>, PhantomData<O>, PhantomData<R>);

impl<I, O, R, P, F> Wrap<I, O, R, P, F> {
    fn new(p: P, f: F) -> Self { Self(p, f, PhantomData, PhantomData, PhantomData) }
}

impl<I, O, E, R, I2, O2, R2, P, F> Pipe<I2, O2, E, R2> for Wrap<I, O, R, P, F>
where
    P: Pipe<I, O, E, R>,
    F: FnMut(&mut P, I2) -> Result<R2, O2, E>,
{
    fn apply(&mut self, input: I2) -> Result<R2, O2, E> { (self.1)(&mut self.0, input) }
}
