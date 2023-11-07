use crate::Pipe;
use fatal_error::FatalError;
use std::error::Error as StdError;

/// Changes error behaviour
pub trait ErrExt<I, O, E, R> {
    /// Makes non fatal errors fatal
    fn escalate(self) -> Escalate<Self>
    where
        Self: Sized,
    {
        Escalate(self)
    }

    /// makes fatal errors non fatal
    fn deescalate(self) -> Deescalate<Self>
    where
        Self: Sized,
    {
        Deescalate(self)
    }
}

impl<I, O, E, R, P> ErrExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [ErrExt::escalate] implementation
pub struct Escalate<P>(P);

impl<I, O, E, R, P: Pipe<I, O, E, R>> Pipe<I, O, E, R> for Escalate<P> {
    fn apply(&mut self, input: I) -> crate::Result<R, O, E> {
        self.0.apply(input).map_err(|x| x.escalate())
    }
}

/// [ErrExt::deescalate] implementation
pub struct Deescalate<P>(P);

impl<I, O, E, R, P: Pipe<I, O, E, R>> Pipe<I, O, E, R> for Deescalate<P> {
    fn apply(&mut self, input: I) -> crate::Result<R, O, E> {
        self.0.apply(input).map_err(|x| x.deescalate())
    }
}

/// Incomplete error
///
/// This error is returned when a pipe needs more input items
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Incomplete {
    /// an unknown number of items is needed
    Unknown,
    /// a minimum of items is needed
    Size(usize),
}

impl std::fmt::Display for Incomplete {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Incomplete::Unknown => write!(f, "more bytes needed"),
            Incomplete::Size(x) => write!(f, "at least {x} more bytes are needed"),
        }
    }
}

impl StdError for Incomplete {}

/// creates a pipe that always return an error
/// ```
/// # use pipe_chain::{error, tag, str::{TagStrError, digits}, OrExt, Pipe, Incomplete, EitherExt};
/// # use fatal_error::FatalError;
/// #[derive(Debug, PartialEq)]
/// enum Error {
///     Tag(TagStrError),
///     Incomplete(Incomplete),
///     Other
/// }
///
/// impl From<TagStrError> for Error { fn from(e: TagStrError) -> Error { Error::Tag(e)} }
///
/// impl From<Incomplete> for Error { fn from(e: Incomplete) -> Error { Error::Incomplete(e) } }
///
/// impl std::error::Error for Error {}
///
/// impl std::fmt::Display for Error {
///    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
///         write!(f, "{self:?}")
///     }
/// }
///
///
/// assert_eq!(tag::<Error, _, _>("a").or(error(|| FatalError::Fatal(Error::Other))).apply("b"), Err(FatalError::Fatal(Error::Other)));
/// ```
pub fn error<I, O, E, R, F>(mut f: F) -> impl Pipe<I, O, E, R>
where
    F: FnMut() -> FatalError<E>,
{
    move |_| Err(f())
}
